theory NominalMultigraph
imports "NomUtil"
begin

class nmts =
fixes prod :: "('a::fs) \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<cdot>" 72)
  and bnd  :: "name \<Rightarrow> 'a \<Rightarrow> 'a" ("\<nu> _ . _" [70,70] 70)
  and id   :: "name \<Rightarrow> name \<Rightarrow> 'a" ("\<delta>[_,_]" [74,74] 80)
  and one  :: 'a ("\<one>")
assumes prod_eqvt: "p \<bullet> (x \<cdot> y) = (p \<bullet> x) \<cdot> (p \<bullet> y)"
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

lemma bnd_prod1: "(atom a) \<sharp> x \<Longrightarrow> \<nu> a . x \<cdot> y = x \<cdot> (\<nu> a . y)"
by (metis atom_name_def bnd_prod prod_comm)

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

lemma id_fr[simp]: "atom c \<sharp> (a,b) \<Longrightarrow> atom c \<sharp> \<delta>[a,b]"
by (auto simp:fr fresh_fun_app[where f = "id a"])

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

lemma prod_fresh[intro]:
  assumes [fr]: "at \<sharp> x"
      and [fr]: "at \<sharp> y"
    shows "at \<sharp> x \<cdot> y"
apply(subst fresh_fun_app[where f = "prod x"])
apply(subst fresh_fun_app[where f = "prod"])
apply(auto simp:prod_eqvt permute_fun_def eqvt_def fr)
done

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
also have "... = dim \<cdot> x" by simp
finally show ?thesis .
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

theorem rnm_prod:
assumes [fr]: "(atom b) \<sharp> a"
shows "[b >> a](x \<cdot> y) = [b >> a]x \<cdot> [b >> a]y"
proof -
obtain c :: name where [fr]: "(atom c) \<sharp> (a, b, x, y)" by (rule obtain_fresh)
have [fr]: "atom c \<sharp> \<delta>[a,b]" by (simp add:fr)
have [fr]: "atom c \<sharp> \<nu> b . \<delta>[a, b] \<cdot> y"
by (metis fr bnd_fr1 fresh_Pair prod_fresh)
have [fr]:"atom b \<sharp> (c, (b \<leftrightarrow> c) \<bullet> y)"
by (metis fr flip_at_simps(2) fresh_Pair fresh_at_base_permute_iff fresh_symm)
have delta:"\<delta>[a,b] \<cdot> \<delta>[b,c] = \<delta>[a,b] \<cdot> \<delta>[a,c]"
by(subst id_swp, auto simp add:fr newfresh)

have "[b >> a](x \<cdot> y) = \<nu> b . \<delta>[a,b] \<cdot> x \<cdot> y" by (simp add:rnm_def)
also have "... = \<nu> b . \<delta>[a,b] \<cdot> x \<cdot> [c >> b]((b \<leftrightarrow> c) \<bullet> y)" by (metis fr rnm_swap permute_flip_cancel)
also have "... = \<nu> b . \<delta>[a,b] \<cdot> x \<cdot> (\<nu> c . \<delta>[b,c] \<cdot> (b \<leftrightarrow> c) \<bullet> y)" by (simp add:rnm_def)
also have "... = \<nu> b . \<nu> c . \<delta>[a,b] \<cdot> x \<cdot> \<delta>[b,c] \<cdot> (b \<leftrightarrow> c) \<bullet> y" by (metis fr fresh_Pair bnd_prod prod_comm)
also have "... = \<nu> b . \<nu> c . \<delta>[a,b] \<cdot> \<delta>[b,c] \<cdot> x \<cdot> (b \<leftrightarrow> c) \<bullet> y" by (metis prod_comm prod_assoc)
also have "... = \<nu> b . \<nu> c . \<delta>[a,b] \<cdot> \<delta>[a,c] \<cdot> x \<cdot> (b \<leftrightarrow> c) \<bullet> y" by (metis delta prod_assoc)
also have "... = \<nu> b . \<delta>[a,b] \<cdot> (\<nu> c . \<delta>[a,c] \<cdot> x \<cdot> (b \<leftrightarrow> c) \<bullet> y)" by (metis fr bnd_prod prod_comm)
also have "... = \<nu> b . \<delta>[a,b] \<cdot> (\<nu> c . x \<cdot> \<delta>[a,c] \<cdot> (b \<leftrightarrow> c) \<bullet> y)" by (metis prod_assoc prod_comm)
also have "... = \<nu> b . (\<delta>[a,b] \<cdot> x) \<cdot> (\<nu> c . \<delta>[a,c] \<cdot> (b \<leftrightarrow> c) \<bullet> y)" by (auto simp:fr bnd_prod1)
also have "... = (\<nu> b . \<delta>[a,b] \<cdot> x) \<cdot> (\<nu> c . \<delta>[a,c] \<cdot> (b \<leftrightarrow> c) \<bullet> y)" by (metis fr bnd_prod bnd_fr1 fresh_Pair id_fr prod_fresh)
also have "... = (\<nu> b . \<delta>[a,b] \<cdot> x) \<cdot> (b \<leftrightarrow> c) \<bullet> (\<nu> b . (b \<leftrightarrow> c) \<bullet> \<delta>[a,c] \<cdot> y)" by (metis bnd_eqvt permute_flip_cancel prod_eqvt flip_at_simps(2))
also have "... = (\<nu> b . \<delta>[a,b] \<cdot> x) \<cdot> (b \<leftrightarrow> c) \<bullet> (\<nu> b . \<delta>[a, b] \<cdot> y)" by (auto simp:flip_fresh_fresh fr)
also have "... = (\<nu> b . \<delta>[a,b] \<cdot> x) \<cdot> (\<nu> b . \<delta>[a, b] \<cdot> y)" by(auto simp:fr flip_fresh_fresh)
also have "... = [b >> a]x \<cdot> [b >> a]y" by (simp add:rnm_def)
finally show ?thesis .
qed

end
