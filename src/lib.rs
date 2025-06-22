use char_classes as cc;

/// # Examples
/// ```
/// use cdecl_to_rsdecl::trim_csi;
/// assert_eq!("hi", trim_csi("\x1b[1;31mhi"));
/// assert_eq!("hi", trim_csi("\x1b[1;31m\x1b[8mhi"));
/// assert_eq!("hi", trim_csi("\x1b[1;31m\x1b[8mhi\x1b[0m"));
/// assert_eq!("hi", trim_csi("\x1b[1;31m\x1b[8mhi\x1b[0m\x1b[0m"));
/// ```
pub fn trim_csi(mut s: &str) -> &str {
    let alpha = cc::any!("a-zA-Z");
    while s.starts_with("\x1b[") {
        s = s.split_once(alpha).unwrap().1
    }
    while s.ends_with(alpha) {
        let part = &s[..s.len()-1];
        let Some(end_csi) = part
            .rsplit_once("\x1b[")
            .map(|it| it.1)
            .filter(|it| !it.contains(alpha))
        else {
            break;
        };
        s = &part[..part.len()-end_csi.len()-2];
    }
    s
}
