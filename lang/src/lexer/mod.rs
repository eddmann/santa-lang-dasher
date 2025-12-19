pub mod token;

pub use token::{Token, TokenKind};
use token::{Position, Span};

#[cfg(test)]
mod tests;

#[derive(Debug)]
pub enum LexError {
    UnexpectedCharacter { ch: char, position: Position },
    UnterminatedString { position: Position },
    InvalidNumber { text: String, position: Position },
}

pub type LexResult = Result<Vec<Token>, LexError>;

pub fn lex(input: &str) -> LexResult {
    let mut lexer = Lexer::new(input);
    lexer.lex_all()
}

struct Lexer {
    input: Vec<char>,
    position: usize,
    line: u32,
    column: u32,
}

impl Lexer {
    fn new(input: &str) -> Self {
        Self {
            input: input.chars().collect(),
            position: 0,
            line: 1,
            column: 1,
        }
    }

    fn lex_all(&mut self) -> LexResult {
        let mut tokens = Vec::new();

        loop {
            self.skip_whitespace();

            if self.is_at_end() {
                let pos = self.current_position();
                tokens.push(Token::new(TokenKind::Eof, Span::new(pos, pos)));
                break;
            }

            tokens.push(self.next_token()?);
        }

        Ok(tokens)
    }

    fn next_token(&mut self) -> Result<Token, LexError> {
        let start = self.current_position();
        let ch = self.peek();

        let kind = match ch {
            // Numbers (integers and decimals)
            '0'..='9' => self.lex_number()?,
            '-' => {
                // Always emit Minus - let parser handle unary minus for negative numbers
                self.advance();
                TokenKind::Minus
            }
            // Strings
            '"' => self.lex_string()?,
            // Identifiers and keywords
            'a'..='z' | 'A'..='Z' => self.lex_identifier_or_keyword()?,
            // Underscore (wildcard, identifier, or start of rest identifier)
            '_' => {
                self.advance();
                // Check if this is a bare underscore or part of an identifier
                if !self.is_at_end() {
                    let next = self.peek();
                    if next.is_ascii_alphanumeric() || next == '_' || next == '?' {
                        // It's an identifier starting with underscore (like _foo, __time_nanos)
                        let mut name = String::from("_");
                        name.push_str(&self.lex_identifier_name()?);
                        TokenKind::Identifier(name)
                    } else {
                        // Just a bare underscore (wildcard/placeholder)
                        TokenKind::Underscore
                    }
                } else {
                    // Underscore at end of input
                    TokenKind::Underscore
                }
            }
            // Single-character operators
            '+' => {
                self.advance();
                TokenKind::Plus
            }
            '*' => {
                self.advance();
                TokenKind::Star
            }
            '/' => {
                self.advance();
                // Check for comment
                if self.peek() == '/' {
                    return Ok(Token::new(self.lex_comment()?, Span::new(start, self.current_position())));
                }
                TokenKind::Slash
            }
            '%' => {
                self.advance();
                TokenKind::Percent
            }
            '!' => {
                self.advance();
                if self.peek() == '=' {
                    self.advance();
                    TokenKind::NotEqual
                } else {
                    TokenKind::Bang
                }
            }
            '=' => {
                self.advance();
                if self.peek() == '=' {
                    self.advance();
                    TokenKind::EqualEqual
                } else {
                    TokenKind::Equal
                }
            }
            '<' => {
                self.advance();
                if self.peek() == '=' {
                    self.advance();
                    TokenKind::LessEqual
                } else {
                    TokenKind::Less
                }
            }
            '>' => {
                self.advance();
                if self.peek() == '=' {
                    self.advance();
                    TokenKind::GreaterEqual
                } else if self.peek() == '>' {
                    self.advance();
                    TokenKind::RightRight
                } else {
                    TokenKind::Greater
                }
            }
            '&' => {
                self.advance();
                if self.peek() == '&' {
                    self.advance();
                    TokenKind::AndAnd
                } else {
                    return Err(LexError::UnexpectedCharacter {
                        ch: '&',
                        position: start,
                    });
                }
            }
            '|' => {
                self.advance();
                if self.peek() == '|' {
                    self.advance();
                    TokenKind::OrOr
                } else if self.peek() == '>' {
                    self.advance();
                    TokenKind::Pipe
                } else {
                    TokenKind::VerticalBar
                }
            }
            '.' => {
                self.advance();
                if self.peek() == '.' {
                    self.advance();
                    if self.peek() == '=' {
                        self.advance();
                        TokenKind::DotDotEqual
                    } else {
                        // Always produce DotDot - the parser handles ..identifier for rest patterns
                        TokenKind::DotDot
                    }
                } else {
                    return Err(LexError::UnexpectedCharacter {
                        ch: '.',
                        position: start,
                    });
                }
            }
            // Delimiters
            '(' => {
                self.advance();
                TokenKind::LeftParen
            }
            ')' => {
                self.advance();
                TokenKind::RightParen
            }
            '[' => {
                self.advance();
                TokenKind::LeftBracket
            }
            ']' => {
                self.advance();
                TokenKind::RightBracket
            }
            '{' => {
                self.advance();
                TokenKind::LeftBrace
            }
            '}' => {
                self.advance();
                TokenKind::RightBrace
            }
            '#' => {
                self.advance();
                if self.peek() == '{' {
                    self.advance();
                    TokenKind::HashBrace
                } else {
                    return Err(LexError::UnexpectedCharacter {
                        ch: '#',
                        position: start,
                    });
                }
            }
            ',' => {
                self.advance();
                TokenKind::Comma
            }
            ':' => {
                self.advance();
                TokenKind::Colon
            }
            ';' => {
                self.advance();
                TokenKind::Semicolon
            }
            '`' => {
                self.advance();
                TokenKind::Backtick
            }
            '@' => {
                self.advance();
                TokenKind::At
            }
            _ => {
                return Err(LexError::UnexpectedCharacter {
                    ch,
                    position: start,
                })
            }
        };

        let end = self.current_position();
        Ok(Token::new(kind, Span::new(start, end)))
    }

    fn lex_identifier_or_keyword(&mut self) -> Result<TokenKind, LexError> {
        let name = self.lex_identifier_name()?;

        // Check if it's a keyword
        let kind = match name.as_str() {
            "let" => TokenKind::Let,
            "mut" => TokenKind::Mut,
            "if" => TokenKind::If,
            "else" => TokenKind::Else,
            "match" => TokenKind::Match,
            "return" => TokenKind::Return,
            "break" => TokenKind::Break,
            "nil" => TokenKind::Nil,
            "true" => TokenKind::True,
            "false" => TokenKind::False,
            _ => TokenKind::Identifier(name),
        };

        Ok(kind)
    }

    fn lex_identifier_name(&mut self) -> Result<String, LexError> {
        let mut name = String::new();

        // First character already validated by caller
        while !self.is_at_end() {
            match self.peek() {
                'a'..='z' | 'A'..='Z' | '0'..='9' | '_' | '?' => {
                    name.push(self.advance());
                }
                _ => break,
            }
        }

        Ok(name)
    }

    fn lex_comment(&mut self) -> Result<TokenKind, LexError> {
        self.advance(); // Skip second '/'

        let mut text = String::new();

        while !self.is_at_end() && self.peek() != '\n' {
            text.push(self.advance());
        }

        Ok(TokenKind::Comment(text))
    }

    fn lex_string(&mut self) -> Result<TokenKind, LexError> {
        let start = self.current_position();
        self.advance(); // Skip opening quote

        let mut value = String::new();

        while !self.is_at_end() {
            let ch = self.peek();

            if ch == '"' {
                self.advance(); // Skip closing quote
                return Ok(TokenKind::String(value));
            }

            if ch == '\\' {
                // Handle escape sequences
                self.advance();
                if self.is_at_end() {
                    return Err(LexError::UnterminatedString { position: start });
                }

                let escaped = match self.peek() {
                    'n' => '\n',
                    't' => '\t',
                    'r' => '\r',
                    'b' => '\u{0008}', // backspace
                    'f' => '\u{000C}', // form feed
                    '"' => '"',
                    '\\' => '\\',
                    _ => {
                        return Err(LexError::UnexpectedCharacter {
                            ch: self.peek(),
                            position: self.current_position(),
                        })
                    }
                };

                value.push(escaped);
                self.advance();
            } else {
                value.push(ch);
                self.advance();
            }
        }

        Err(LexError::UnterminatedString { position: start })
    }

    fn lex_number(&mut self) -> Result<TokenKind, LexError> {
        let start = self.current_position();
        let mut text = String::new();
        let mut has_decimal_point = false;

        // Collect digits with optional underscores
        while !self.is_at_end() {
            match self.peek() {
                '0'..='9' => text.push(self.advance()),
                '_' => {
                    self.advance(); // Skip underscores
                }
                '.' => {
                    // Look ahead to distinguish between decimal point and range operator
                    if self.position + 1 < self.input.len() {
                        let next_char = self.input[self.position + 1];
                        if next_char.is_ascii_digit() {
                            // This is a decimal point
                            text.push(self.advance());
                            has_decimal_point = true;
                        } else {
                            // This is a range operator
                            break;
                        }
                    } else {
                        // At end of input, not a decimal
                        break;
                    }
                }
                _ => break,
            }
        }

        // Parse based on whether we saw a decimal point
        if has_decimal_point {
            text.parse::<f64>()
                .map(TokenKind::Decimal)
                .map_err(|_| LexError::InvalidNumber { text, position: start })
        } else {
            text.parse::<i64>()
                .map(TokenKind::Integer)
                .map_err(|_| LexError::InvalidNumber { text, position: start })
        }
    }

    fn current_position(&self) -> Position {
        Position::new(self.line, self.column)
    }

    fn is_at_end(&self) -> bool {
        self.position >= self.input.len()
    }

    fn skip_whitespace(&mut self) {
        while !self.is_at_end() {
            match self.peek() {
                ' ' | '\t' | '\r' | '\n' => {
                    if self.peek() == '\n' {
                        self.line += 1;
                        self.column = 1;
                        self.position += 1;
                    } else {
                        self.column += 1;
                        self.position += 1;
                    }
                }
                _ => break,
            }
        }
    }

    fn peek(&self) -> char {
        self.input.get(self.position).copied().unwrap_or('\0')
    }

    fn advance(&mut self) -> char {
        let ch = self.peek();
        self.position += 1;
        self.column += 1;
        ch
    }
}
