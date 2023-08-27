pub struct EscapeIter<T> 
    where T: std::iter::Iterator<Item= char> {
    inner: T,
    escaped: bool
}

pub fn escape_str(input: &str) -> EscapeIter<std::str::Chars> {
    EscapeIter {
        inner: input.chars(),
        escaped: false
    }
}

pub fn escape_vec(input: &Vec<char>) -> EscapeIter<impl Iterator<Item=char> +'_> {
    EscapeIter {
        inner: input.iter().map(|x: &char| *x),
        escaped: false
    }
}

pub fn escape_slice(input: &[char]) -> EscapeIter<impl Iterator<Item=char> +'_> {
    EscapeIter {
        inner: input.iter().map(|x: &char| *x),
        escaped: false
    }
}

impl<T> std::iter::Iterator for EscapeIter<T>
    where T: std::iter::Iterator<Item= char> {
    type Item = (char, bool);
    fn next(&mut self) -> Option<(char, bool)> {
        loop {
            match self.inner.next() {
                Some(c) if self.escaped => {
                    self.escaped = false;
                    return Some((c, true))
                },
                Some('\\') => {
                    self.escaped = true;
                },
                Some(c) => {
                    return Some((c, false))
                },
                None => {
                    return None
                }
            }
        }
    }
}

pub fn find_right_delimiter(input: &Vec<char>, start: usize, left: char, right: char) -> Option<usize> {
    let mut depth = 0;
    let mut input_iter = escape_slice(&input[start..]);
    let mut i = start; // Need to keep track of index since backslashes wouldn't be counted in enumerate
    for (c, escaped) in input_iter {
        if !escaped {
            if c == left {
                depth += 1;
            } else if c == right {
                if depth == 1 {
                    return Some(i)
                }
                depth -= 1;
            }
        }
        i += 1;
    }
    None
}