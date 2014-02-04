theory NomUtil
imports "../nominal2/Nominal/Nominal2"
begin

atom_decl name

lemma fresh_symm:
  assumes "atom (a::name) \<sharp> (b::name)"
  shows "atom b \<sharp> a"
using assms
by simp

theorems newfresh = fresh_Nil fresh_Pair fresh_Cons swap_fresh_fresh flip_def fresh_append

lemma permute_flip:
  "\<pi> \<bullet> (a \<leftrightarrow> b) \<bullet> s = (\<pi> \<bullet> a \<leftrightarrow> \<pi> \<bullet> b) \<bullet> \<pi> \<bullet> s"
by (metis flip_eqvt permute_eqvt)

end
