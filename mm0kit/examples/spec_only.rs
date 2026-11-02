//! Parse an `.mm0` spec and write the statements back out as an `.mmb`.
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let src = std::fs::read_to_string(&args[1]).unwrap();
    let mut env = mm0kit::env::Env::new();
    mm0kit::parse::parse_into(&mut env, &src).unwrap();
    std::fs::write(&args[2], mm0kit::mmb::write(&env)).unwrap();
    eprintln!("{} sorts, {} terms, {} theorems", env.sorts.len(), env.terms.len(), env.thms.len());
}
