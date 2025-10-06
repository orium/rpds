use super::*;
use archery::RcK;
use pretty_assertions::assert_eq;

#[test]
fn test_replace() {
    let src: SharedPointer<_, RcK> = SharedPointer::new(3);
    let mut dest = 0;

    replace(&mut dest, src);

    assert_eq!(dest, 3);
}
