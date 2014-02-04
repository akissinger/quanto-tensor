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
theorems supp_args = supports_def permute_fun_def fresh_def[symmetric] swap_fresh_fresh finite_supp


lemma permute_flip:
  "\<pi> \<bullet> (a \<leftrightarrow> b) \<bullet> s = (\<pi> \<bullet> a \<leftrightarrow> \<pi> \<bullet> b) \<bullet> \<pi> \<bullet> s"
by (metis flip_eqvt permute_eqvt)

ML {*
fun name_from_fresh_thm thm = case prop_of thm of @{const HOL.Trueprop} $
  ((Const ("Nominal2_Base.pt_class.fresh", _) $ (@{const atom(name)} $ n) $ _))
  => SOME n | _ => NONE;

(* TODO: add some automatic simplification when rules are tagged 'fr', e.g. to add
 * symmetric freshness conditions and simplify expressions involving lists, pairs, etc. *)
structure FreshRules = Named_Thms(
  val name = @{binding fr}
  val description = "Local freshness assumptions"
)
*}

setup {* FreshRules.setup *}

end
