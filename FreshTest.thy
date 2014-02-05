theory FreshTest
imports TensorMonoid
begin

lemma nmult_assoc1:
  assumes "atom n \<sharp> (y::name, z::name, xs::name list, a::name)"
  shows "P"
proof -
  let ?free = "(y,z,xs,a)"
  (* define some temporary fresh names for the calculation *)
  note [fr] = assms
  obtain n1::name where [fr]:"atom n1 \<sharp> ?free" by (rule obtain_fresh) let ?free = "(?free,n1)"
  obtain n2::name where [fr]:"atom n2 \<sharp> ?free" by (rule obtain_fresh) let ?free = "(?free,n2)"
  have [fr]:"atom n1 \<sharp> n2" by (simp only:fr fresh_symm)

ML_prf {*
(* experimenting with pre-simplifying fresh rules in ML, and pulling names *)
val frs = FreshRules.get @{context};
val t = nth (FreshRules.get @{context}) 1;

local val rules = @{thms fresh_Pair[THEN eq_reflection] fresh_Cons[THEN eq_reflection] fresh_append[THEN eq_reflection]};
in val list = HOLogic.conj_elims (Raw_Simplifier.rewrite_rule rules t);
end

local
val names = map_filter name_from_fresh_thm (FreshRules.get @{context});
in val cnames = map (cterm_of @{theory}) names;
end
*}
oops

end
