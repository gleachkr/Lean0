//! Build a few theorems over `lean.mm0` with the provers and write `.mm0` + `.mmb`.
use mm0kit::env::*;
use mm0kit::mmb;
use mm0kit::lean::Lean;
use mm0kit::level::Levels;
use mm0kit::bin::Rel;
use num_bigint::BigUint;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let src = std::fs::read_to_string(&args[1]).unwrap();
    let mut env = Env::new();
    mm0kit::parse::parse_into(&mut env, &src).unwrap();
    let mut lean = Lean::new(&mut env);
    let mut lv = Levels::new();
    let n_spec = env.order.len();
    let (ctx, lvl) = (env.sort_names["ctx"], env.sort_names["lvl"]);

    // leqv (limax (ls u) (ls v)) (ls (lmax u v)), and a messier one
    let (u, v) = (env.var(0), env.var(1));
    let cases: Vec<(&str, E, E)> = {
        let su = env.app_n("ls", &[u]);
        let sv = env.app_n("ls", &[v]);
        let a = env.app_n("limax", &[su, sv]);
        let m = env.app_n("lmax", &[u, v]);
        let b = env.app_n("ls", &[m]);
        let z = env.app_n("lz", &[]);
        let sz = env.app_n("ls", &[z]);
        let ssu = env.app_n("ls", &[su]);
        let c1 = env.app_n("lmax", &[sz, v]);
        let c2 = env.app_n("lmax", &[u, c1]);
        let c = env.app_n("lmax", &[c2, ssu]); // max (max u (max 1 v)) (u+2)
        let d1 = env.app_n("lmax", &[v, ssu]);
        let d = env.app_n("limax", &[sz, d1]); // imax 1 (max v (u+2))
        // the laws the audit (§3) found underivable without case splits
        let iuv = env.app_n("limax", &[u, v]);
        let ivu = env.app_n("limax", &[v, u]);
        let e1 = env.app_n("lmax", &[u, iuv]); // max u (imax u v) ≈ max u v
        let muv = env.app_n("lmax", &[u, v]);
        let e2 = env.app_n("limax", &[u, muv]); // imax u (max u v) ≈ max u v
        let e3 = env.app_n("lmax", &[iuv, ivu]); // max (imax u v) (imax v u) ≈ max u v
        let e4 = env.app_n("limax", &[iuv, v]); // imax (imax u v) v ≈ imax u v
        vec![("lv1", a, b), ("lv2", c, d), ("lv3", e1, muv), ("lv4", e2, muv), ("lv5", e3, muv), ("lv6", e4, iuv)]
    };
    for (name, a, b) in cases {
        lean.reset();
        lv.reset();
        let p = lv.equiv(&lean, &mut env, a, b).unwrap();
        let concl = env.app_n("leqv", &[a, b]);
        let p = env.convert(p, concl).unwrap();
        env.add_thm(ThmDecl { name: name.into(), args: vec![("u".into(), lvl), ("v".into(), lvl)].into(), hyps: Box::new([]), concl, axiom: false, local: false, proof: Some(p), doc: None }).unwrap();
    }

    // ty G (srt u) (srt (ls u)), through a beta step: (λ x: Sort u. x) (Sort u) ≡ Sort u : Sort (u+1)
    lean.reset();
    let (g, u) = (env.var(0), env.var(1));
    let su = lean.srt(&mut env, u);
    let lu = env.app_n("ls", &[u]);
    let ssu = lean.srt(&mut env, lu);
    let refl_u = lv.equiv(&lean, &mut env, u, u).unwrap();
    let ty_su = lean.sort_df(&mut env, g, u, u, refl_u).unwrap();
    // body x : Sort u in context (cons (srt u) G)
    let g1 = lean.cons(&mut env, su, g);
    let ty_x = lean.bvar_rule(&mut env, g1, 0).unwrap();
    // the argument `Sort l` with l : Sort l+1 would not fit; use the argument `x`'s type: apply to a Sort u inhabitant
    let _ = ty_x;
    let concl = env.app_n("ty", &[g, su, ssu]);
    let p = env.convert(ty_su, concl).unwrap();
    env.add_thm(ThmDecl { name: "srt_ty".into(), args: vec![("G".into(), ctx), ("u".into(), lvl)].into(), hyps: Box::new([]), concl, axiom: false, local: false, proof: Some(p), doc: None }).unwrap();

    // deq G (app (lam (srt u) (lam (bvar 0) (bvar 0))) (pi (srt u)...)): a β-step with lift/inst under binders
    // id_u := λ (A: Sort u). λ (a: A). a  ;  check  id_u (Sort u -> ...) — keep it simple: (λ A. λ a:A. a) applied to `srt lz` at u := 1
    lean.reset();
    let g = env.var(0);
    let z = env.app_n("lz", &[]);
    let one = env.app_n("ls", &[z]);
    let s0 = lean.srt(&mut env, z); // Prop : Sort 1
    let s1 = lean.srt(&mut env, one);
    let b0 = lean.bvar(&mut env, 0);
    let inner = lean.lam(&mut env, b0, b0); // λ a: #0. a
    let idf = lean.lam(&mut env, s1, inner);
    // typing of body `inner` in context (cons (srt 1) G): λ a:#0. a : pi #0 #1
    let g1 = lean.cons(&mut env, s1, g);
    let r0 = lv.equiv(&lean, &mut env, z, z).unwrap();
    let pa = {
        let b0ty = lean.bvar_rule(&mut env, g1, 0).unwrap(); // #0 : srt 1 (lifted, closed)
        b0ty
    };
    let g2 = lean.cons(&mut env, b0, g1);
    let pv = lean.bvar_rule(&mut env, g2, 0).unwrap(); // #0 : #1
    let pinner = lean.lam_df(&mut env, pa, pv).unwrap();
    let parg = lean.sort_df(&mut env, g, z, z, r0).unwrap(); // srt 0 : srt 1
    let app = lean.app(&mut env, idf, s0);
    let pb = lean.beta(&mut env, pinner, parg).unwrap();
    let (_, _, r, rt) = lean.deq_parts(&mut env, pb);
    println!("beta: {} ~> {} : {}", env.show(app, &["G"]), env.show(r, &["G"]), env.show(rt, &["G"]));
    let concl = env.concl(pb);
    env.add_thm(ThmDecl { name: "beta_ex".into(), args: vec![("G".into(), ctx)].into(), hyps: Box::new([]), concl, axiom: false, local: false, proof: Some(pb), doc: None }).unwrap();

    // binary arithmetic, including carries, zeros and a 130-bit product
    let mut bins = mm0kit::bin::Bins::new(&env);
    let big = (BigUint::from(1u32) << 64u32) - 1u32;
    let cases: Vec<(Rel, Vec<BigUint>)> = vec![
        (Rel::Succ, vec![BigUint::from(7u32)]),
        (Rel::Add, vec![BigUint::from(0u32), BigUint::from(5u32)]),
        (Rel::Add, vec![big.clone(), BigUint::from(1u32)]),
        (Rel::AddC, vec![big.clone(), big.clone()]),
        (Rel::Mul, vec![big.clone(), BigUint::from(12345u32) << 70u32]),
        (Rel::Mul, vec![BigUint::from(0u32), BigUint::from(6u32)]),
        (Rel::Pow, vec![BigUint::from(3u32), BigUint::from(40u32)]),
        (Rel::Pow, vec![BigUint::from(0u32), BigUint::from(0u32)]),
        (Rel::And, vec![BigUint::from(0b1100u32), BigUint::from(0b1010u32)]),
        (Rel::And, vec![BigUint::from(0b100u32), BigUint::from(0b011u32)]),
        (Rel::Or, vec![BigUint::from(0b1100u32), BigUint::from(0b1010u32)]),
        (Rel::Xor, vec![BigUint::from(0b1100u32), BigUint::from(0b1100u32)]),
        (Rel::Xor, vec![big.clone(), BigUint::from(0b1010u32)]),
    ];
    for (i, (rel, ins)) in cases.into_iter().enumerate() {
        let (r, p) = bins.rel(&mut env, rel, &ins).unwrap();
        let concl = env.concl(p);
        let last = *env.head(concl).unwrap().1.last().unwrap();
        assert_eq!(bins.val(&env, last), Some(r.clone()), "{rel:?} {ins:?}");
        assert_eq!(last, bins.num(&mut env, &r), "{rel:?} {ins:?}: result not canonical");
        env.add_thm(ThmDecl { name: format!("bin{i}").into(), args: vec![].into(), hyps: Box::new([]), concl, axiom: false, local: false, proof: Some(p), doc: None }).unwrap();
    }

    let mut text = src.clone();
    for &st in &env.order[n_spec..] {
        if let Some(t) = env.stmt_text(st) {
            text.push('\n');
            text.push_str(&t);
        }
    }
    std::fs::write(&args[2], text).unwrap();
    std::fs::write(&args[3], mmb::write(&env)).unwrap();
    eprintln!("{} expr nodes, {} proof nodes", env.num_nodes(), env.num_pfs());
}
