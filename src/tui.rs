use std::{borrow::Cow, cell::RefCell, rc::Rc};

use rustyline::{
    highlight::Highlighter,
    validate::{ValidationResult, Validator},
};
use rustyline_derive::{Completer, Helper, Hinter};

use crate::{
    builtins,
    parser::{ParserTokenKind, TokenIterator},
    process_input,
    state::{CalculatorState, Value},
    stringify_output, DEFAULT_PRECISION,
};

#[derive(Completer, Helper, Hinter)]
pub struct TuiHelper {
    pub state: Rc<RefCell<CalculatorState>>,
}

impl Validator for TuiHelper {
    fn validate(
        &self,
        ctx: &mut rustyline::validate::ValidationContext,
    ) -> rustyline::Result<rustyline::validate::ValidationResult> {
        let prefix = "\t\t\t";

        let mut state = self.state.borrow_mut();
        match process_input(&mut state, ctx.input(), true) {
            Ok(Some((val, fmt))) => Ok(ValidationResult::Valid(Some(format!(
                "{prefix}(Current result: {})",
                stringify_output(val, fmt, true).unwrap()
            )))),
            Ok(None) => Ok(ValidationResult::Valid(None)),
            Err(e) => Ok(ValidationResult::Invalid(Some(format!("{prefix}({e})")))),
        }
    }

    fn validate_while_typing(&self) -> bool {
        true
    }
}

impl Highlighter for TuiHelper {
    fn highlight<'l>(
        &self,
        line: &'l str,
        mut pos: usize,
        submit: bool,
    ) -> std::borrow::Cow<'l, str> {
        if pos > 0 && !matches!(line.as_bytes().get(pos), Some(b'(' | b')')) {
            pos -= 1;
        }

        let mut state = self.state.borrow_mut();
        let (mut line, pos) = color_individual_glyphs(&line, pos, &mut state);

        if !submit {
            line = highlight_matching_paren(line, pos);
        }

        line = highlight_mismatched_parens(&line);

        Cow::Owned(line)
    }

    fn highlight_char(&self, _line: &str, _pos: usize) -> bool {
        true
    }

    fn highlight_prompt<'b, 's: 'b, 'p: 'b>(
        &'s self,
        prompt: &'p str,
        default: bool,
    ) -> Cow<'b, str> {
        let _ = default;
        Cow::Borrowed(prompt)
    }

    fn highlight_hint<'h>(&self, hint: &'h str) -> Cow<'h, str> {
        Cow::Borrowed(hint)
    }

    fn highlight_candidate<'c>(
        &self,
        candidate: &'c str, // FIXME should be Completer::Candidate
        completion: rustyline::CompletionType,
    ) -> Cow<'c, str> {
        let _ = completion;
        Cow::Borrowed(candidate)
    }
}

/// Applies syntax higlighting to the entire line, and at the same time,
/// computes the index the cursor would be at after all the inserts.
fn color_individual_glyphs(line: &str, pos: usize, state: &mut CalculatorState) -> (String, usize) {
    let error_span = {
        let syntax_check_result = process_input(state, line, true);
        if let Err(e) = syntax_check_result {
            e.span
        } else {
            0..0
        }
    };

    let mut output = String::with_capacity(5 * line.len());

    let mut new_pos = pos;

    let mut tokens = TokenIterator::of(line, DEFAULT_PRECISION);
    let mut cursor = 0;
    while let Some(token) = tokens.next() {
        let (start, end) = (cursor, tokens.position());
        let span = token.as_ref().map_or(start..end, |tok| tok.span.clone());
        let segment = &line[start..end];
        cursor = end;

        let token = match token {
            Ok(token) => token,
            Err(..) => {
                // Unrecognized, but don't do error checking here - `process_input()` already outputs actual errors.
                output += "\x1b[0m";
                output += segment;
                continue;
            }
        };

        let color = match token.kind {
            ParserTokenKind::LeftParen | ParserTokenKind::RightParen => "\x1b[38;5;6m",
            ParserTokenKind::Function { name } => {
                if builtins::resolve_builtin_fn_call(name).is_some() {
                    "\x1b[38;5;12;1m"
                } else {
                    "\x1b[38;5;12m"
                }
            }
            ParserTokenKind::Variable { name } => {
                if state.variables.contains_key(name) {
                    "\x1b[38;5;13;1m" // bold constants
                } else {
                    "\x1b[38;5;13m"
                }
            }
            ParserTokenKind::BinaryOperator(..) => "\x1b[38;5;248m",
            ParserTokenKind::Number(Value::Boolean(_)) => "\x1b[38;5;3m",
            _ => "\x1b[0m",
        };

        output += color;

        if span.start < error_span.end && span.end > error_span.start {
            let mut estart = error_span.start.saturating_sub(span.start);
            let mut eend = (estart + error_span.end - error_span.start).min(span.end - span.start);
            estart += span.start - start;
            eend += span.start - start;
            output += &segment[..estart];
            output += "\x1b[48;5;52m";
            output += &segment[estart..eend];
            output += "\x1b[0m";
            output += color;
            output += &segment[eend..];
        } else {
            output += segment;
        }

        // Found the segment the cursor was in: compute where it's now
        if pos >= start && pos < end {
            new_pos = output.len() - segment.len() + pos - start;
        }
    }

    (output + "\x1b[0m", new_pos)
}

fn highlight_matching_paren(line: String, pos: usize) -> String {
    let bytes = line.as_bytes();
    match bytes.get(pos) {
        Some(b')') => {
            // Find matching paren
            let mut stack = 1;
            let mut cursor = pos;
            while stack != 0 && cursor != 0 {
                cursor -= 1;
                match bytes[cursor] {
                    b'(' => stack -= 1,
                    b')' => stack += 1,
                    _ => {}
                }
            }

            if stack == 0 && bytes[cursor] == b'(' {
                return highlight_parens(&line, cursor, pos);
            }
        }
        Some(b'(') => {
            let mut stack = 1;
            let mut cursor = pos;
            while stack != 0 && cursor + 1 < bytes.len() {
                cursor += 1;
                match bytes[cursor] {
                    b'(' => stack += 1,
                    b')' => stack -= 1,
                    _ => {}
                }
            }

            if stack == 0 && bytes[cursor] == b')' {
                return highlight_parens(&line, pos, cursor);
            }
        }
        _ => {}
    }
    line
}

fn highlight_parens(line: &str, left: usize, mut right: usize) -> String {
    right -= left;

    let (left, rest) = line.split_at(left);
    let (mid, right) = rest.split_at(right);

    // Skip the actual parens
    let (mid, right) = (&mid[1..], &right[1..]);

    format!("{left}\x1b[38;5;14;1m(\x1b[0;38;5;6m{mid}\x1b[1;38;5;14m)\x1b[0;38;5;6m{right}")
}

/// Rather than highlighting the paren that matches with the one next to the cursor like
/// `highlight_matching_paren`, this colors all parens without a matching pair in red.
fn highlight_mismatched_parens(line: &str) -> String {
    let mut result = line.to_owned();

    let mut stack = 0;
    for (i, c) in line.bytes().enumerate().rev() {
        if c == b'(' {
            stack -= 1;
        } else if c == b')' {
            stack += 1;
        } else {
            continue;
        }

        if stack < 0 {
            result.insert_str(i + 1, "\x1b[m");
            result.insert_str(i, "\x1b[38;5;1m");
            stack = 0;
        }
    }

    let line = result.clone();
    let mut stack = 0;
    let mut offset = 0;
    for (mut i, c) in line.bytes().enumerate() {
        if c == b'(' {
            stack += 1;
        } else if c == b')' {
            stack -= 1;
        } else {
            continue;
        }

        if stack < 0 {
            i += offset;
            result.insert_str(i + 1, "\x1b[m");
            result.insert_str(i, "\x1b[38;5;1m");
            offset += "\x1b[m\x1b[38;5;1m".len();
            stack = 0;
        }
    }

    result
}
