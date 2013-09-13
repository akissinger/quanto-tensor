theory DoubleBinder
imports "../Nominal/Nominal2"
begin

atom_decl uname
atom_decl dname

nominal_datatype monoid =
  COMBINE "monoid" "monoid" (infixr "\<cdot>" 150)
| K "x"::uname "y"::dname "t"::monoid binds x in t ("K<_ _> _" [200,200,200] 200)
| ID "dname" "uname" ("id|_|_|" [200,200] 300)
| MULT "dname" "dname" "uname" ("m|_ _|_|" [200,200,200] 300)
| UNIT "uname" ("u|_|" [200] 300)

term "K<a b> u|a| \<cdot> m|b c|d|"

theorems newfresh = fresh_Nil fresh_Pair fresh_Cons swap_fresh_fresh flip_def fresh_append

inductive
  tens_eq :: "monoid \<Rightarrow> monoid \<Rightarrow> bool" (infix "\<approx>" 50)
where
  tens_eq_refl[intro]: "s = t \<Longrightarrow> s \<approx> t"
| tens_eq_trans[intro,trans]: "s \<approx> t \<Longrightarrow> t \<approx> u \<Longrightarrow> s \<approx> u"
| tens_eq_sym[intro]: "s \<approx> t \<Longrightarrow> t \<approx> s"
| tens_comm[simp]: "s \<cdot> t \<approx> t \<cdot> s"
| tens_assoc[simp]: "(s \<cdot> t) \<cdot> u \<approx> s \<cdot> t \<cdot> u"
| tens_dist[simp]: "atom a \<sharp> s \<Longrightarrow> atom b \<sharp> s \<Longrightarrow> s \<cdot> (K<a b> t) \<approx> K<a b> s \<cdot> t"
| tens_bnd_swap[intro]: "a \<noteq> c \<Longrightarrow> b \<noteq> d \<Longrightarrow> K<a b> K<c d> s \<approx> K<c d> K<a b> s"
| tens_pr_sub[intro]: "s \<approx> t \<Longrightarrow> u \<cdot> s \<approx> u \<cdot> t"
| tens_bnd_sub[intro]: "s \<approx> t \<Longrightarrow> K<a b> s \<approx> K<a b> t"
| id_pre[intro]: "atom a \<sharp> s \<Longrightarrow> K<b c> id|a|b| \<cdot> s \<approx> (a \<leftrightarrow> c) \<bullet> s"
| id_post[intro]: "atom c \<sharp> s \<Longrightarrow> K<a b> s \<cdot> id|b|c| \<approx> (c \<leftrightarrow> a) \<bullet> s"
| mult_assoc[simp]:
    "K<x y> m|a b|x| \<cdot> m|y c|d| \<approx>
     K<x y> m|b c|x| \<cdot> m|a y|d|"
| mult_unit[simp]:
    "K<x y> u|x| \<cdot> m|y a|b| \<approx> id|a|b|"

end
