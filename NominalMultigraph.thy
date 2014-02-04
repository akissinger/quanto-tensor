theory NominalMultigraph
imports "../nominal2/Nominal/Nominal2"
begin

atom_decl name

class nmts =
fixes prod :: "('a::pt) \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<cdot>" 72)
  and bnd  :: "name \<Rightarrow> 'a \<Rightarrow> 'a" ("\<nu> _ . _" [70,70] 70)
  and id   :: "name \<Rightarrow> name \<Rightarrow> 'a" ("\<delta>[_,_]" [74,74] 80)
  and one  :: 'a ("\<one>")
assumes supp_fin: "finite (supp (x::'a))"
    and prod_eqvt: "p \<bullet> (x \<cdot> y) = (p \<bullet> x) \<cdot> (p \<bullet> y)"
    and bnd_eqvt[eqvt]: "p \<bullet> (\<nu> a . x) = \<nu> p \<bullet> a . p \<bullet> x"
    and id_eqvt[eqvt]: "p \<bullet> \<delta>[a,b] = \<delta>[p \<bullet> a,p \<bullet> b]"
    and bnd_fresh: "(atom a) \<sharp> (\<nu> a . x)"
    and prod_assoc: "(x \<cdot> y) \<cdot> z = x \<cdot> y \<cdot> z"
    and prod_unit: "x \<cdot> \<one> = x"
    and prod_comm: "x \<cdot> y = y \<cdot> x"
    and bnd_prod: "(atom a) \<sharp> y \<Longrightarrow> \<nu> a . x \<cdot> y = (\<nu> a . x) \<cdot> y"
    and bnd_bnd: "\<nu> a . \<nu> b . x = \<nu> b . \<nu> a . x"
    and id_refl: "\<delta>[a,a] = \<one>"
    and id_idem[simp]: "\<delta>[a,b] \<cdot> \<delta>[a,b] = \<delta>[a,b]"
    and id_elim: "(atom b) \<sharp> a \<Longrightarrow> \<nu> b . \<delta>[a,b] = \<one>"
    and id_swp[intro]: "\<delta>[a,b] \<cdot> x = \<delta>[a,b] \<cdot> ((a \<leftrightarrow> b) \<bullet> x)"

lemma id_symm: "\<delta>[a,b] = \<delta>[b,a]"
proof -
have "\<delta>[a,b] = \<delta>[a,b] \<cdot> \<delta>[a,b]" by simp
also have "... = \<delta>[a,b] \<cdot> ((a \<leftrightarrow> b) \<bullet> \<delta>[a,b])" by rule

end
