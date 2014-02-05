theory NominalMultigraph
imports "NomUtil"
begin

class nmts =
fixes prod :: "('a::pt) \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<cdot>" 72)
  and bnd  :: "name \<Rightarrow> 'a \<Rightarrow> 'a" ("\<nu> _ . _" [70,70] 70)
  and id   :: "name \<Rightarrow> name \<Rightarrow> 'a" ("\<delta>[_,_]" [74,74] 80)
  and one  :: 'a ("\<one>")
assumes supp_fin: "finite (supp (x::'a))"
    and prod_eqvt: "p \<bullet> (x \<cdot> y) = (p \<bullet> x) \<cdot> (p \<bullet> y)"
    and bnd_eqvt[eqvt]: "p \<bullet> (\<nu> a . x) = \<nu> p \<bullet> a . p \<bullet> x"
    and id_eqvt[eqvt]: "p \<bullet> \<delta>[a,b] = \<delta>[p \<bullet> a,p \<bullet> b]"
    and one_eqvt[eqvt]: "p \<bullet> \<one> = \<one>"
    and bnd_fresh[intro,simp]: "(atom a) \<sharp> (\<nu> a . x)"
    and prod_assoc[simp]: "(x \<cdot> y) \<cdot> z = x \<cdot> y \<cdot> z"
    and prod_unit[simp]: "x \<cdot> \<one> = x"
    and prod_comm[intro]: "x \<cdot> y = y \<cdot> x"
    and bnd_prod: "(atom a) \<sharp> y \<Longrightarrow> \<nu> a . x \<cdot> y = (\<nu> a . x) \<cdot> y"
    and bnd_bnd: "\<nu> a . \<nu> b . x = \<nu> b . \<nu> a . x"
    and id_refl[simp]: "\<delta>[a,a] = \<one>"
    and id_idem[simp]: "\<delta>[a,b] \<cdot> \<delta>[a,b] = \<delta>[a,b]"
    and id_elim[elim]: "(atom b) \<sharp> a \<Longrightarrow> \<nu> b . \<delta>[a,b] = \<one>"
    and id_swp[intro]: "\<delta>[a,b] \<cdot> x = \<delta>[a,b] \<cdot> ((a \<leftrightarrow> b) \<bullet> x)"

lemma id_swp2[intro]: "x \<cdot> \<delta>[a,b] = ((a \<leftrightarrow> b) \<bullet> x) \<cdot> \<delta>[a,b]"
by (metis id_swp prod_comm)

lemma id_symm[intro]: "\<delta>[a,b] = \<delta>[b,a]"
proof -
have "\<delta>[a,b] = \<delta>[a,b] \<cdot> \<delta>[a,b]" by simp
also have "... = \<delta>[a,b] \<cdot> ((a \<leftrightarrow> b) \<bullet> \<delta>[a,b])" by rule
also have "... = \<delta>[a,b] \<cdot> \<delta>[b,a]" by simp
also have "... = ((b \<leftrightarrow> a) \<bullet> \<delta>[a,b]) \<cdot> \<delta>[b,a]" by rule
also have "... = \<delta>[b,a]" by simp
finally show ?thesis .
qed

lemma prod_unit1[simp]: "\<one> \<cdot> x = x"
by (metis prod_comm prod_unit)

lemma supp_one[simp]: "supp \<one> = {}"
by(simp add:eqvt_def supp_fun_eqvt)

lemma bnd_fr1[intro]:
  assumes [fr]: "at \<sharp> x"
  shows "at \<sharp> \<nu> a . x"
proof(cases "(atom a) = at")
case True
  then show ?thesis by auto
next
case False
  then have [fr]: "at \<sharp> a" by simp
  thus ?thesis
    apply(subst fresh_fun_app[where ?f = "bnd a"])
    apply(simp_all add:fr)
  done
qed

lemma bnd_supp[simp]: "supp (\<nu> a . x) \<subseteq> supp x"
by (auto, metis bnd_fr1 fresh_def)

lemma bnd_alpha:
  assumes [fr]: "(atom b) \<sharp> x"
  shows "\<nu> a . x = \<nu> b . (a \<leftrightarrow> b) \<bullet> x"
proof -
from fr have [fr]: "(atom b) \<sharp> \<nu> a . x" by rule
have "\<nu> a . x = (a \<leftrightarrow> b) \<bullet> (\<nu> a . x)" by (subst flip_fresh_fresh, simp_all add:fr)
also have "... =  \<nu> b . (a \<leftrightarrow> b) \<bullet> x" by simp
finally show ?thesis .
qed

definition rnm :: "name \<Rightarrow> name \<Rightarrow> ('a::nmts) \<Rightarrow> 'a" ("[_ >> _]_" [74,74,74] 80)
where "[b >> a]x = \<nu> b . \<delta>[a,b] \<cdot> x"

definition dim :: "'a ::nmts"
where "dim = (FRESH a . \<nu> a . \<one>)"

lemma dim_simp[simp]: "\<nu> a . \<one> = dim"
by(auto simp:dim_def Fresh_apply')

lemma dim_eqvt[eqvt]: "p \<bullet> dim = dim"
by (metis bnd_eqvt dim_simp one_eqvt)

lemma supp_dim[simp]: "supp(dim) = {}"
by (metis bnd_supp dim_simp subset_empty supp_one)

theorem gc:
  assumes [fr]: "(atom a) \<sharp> x"
  shows "\<nu> a . x = dim \<cdot> x"
proof -
have "\<nu> a . x = \<nu> a . \<one> \<cdot> x" by (metis prod_comm prod_unit)
also have "... = (\<nu> a . \<one>) \<cdot> x" by (metis assms bnd_prod) 
finally show ?thesis by simp
qed

theorem rnm_swap:
  assumes [fr]: "(atom a) \<sharp> (b,x)"
    shows "[b >> a]x = (a \<leftrightarrow> b) \<bullet> x"
proof -
have [fr]: "(atom b) \<sharp> (a \<leftrightarrow> b) \<bullet> x"
by (metis assms atom_eqvt flip_at_simps(1) fresh_PairD(2) fresh_permute_iff)
have "[b >> a]x = \<nu> b . \<delta>[a,b] \<cdot> x" by (metis rnm_def)
also have "... = \<nu> b . \<delta>[a,b] \<cdot> (a \<leftrightarrow> b) \<bullet> x" by (metis id_swp)
also have "... = (\<nu> b . \<delta>[a,b]) \<cdot> (a \<leftrightarrow> b) \<bullet> x" by (metis bnd_prod fr)
also have "... = \<one> \<cdot> (a \<leftrightarrow> b) \<bullet> x" by (metis assms fresh_Pair fresh_symm id_elim fr)
also have "... = (a \<leftrightarrow> b) \<bullet> x" by simp
finally show ?thesis .
qed

end
