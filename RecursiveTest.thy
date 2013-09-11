theory RecursiveTest
imports "TensorMonoid"
begin

primrec nmultf :: "name list \<Rightarrow> name \<Rightarrow> monoid"
where
  "nmultf [] a = u<a>"
| "nmultf (x # xs) a = (FRESH y . bnd y . m<x, y><a> \<cdot> nmultf xs y)"

lemma nmultf_eqvt[eqvt]:
  shows "p \<bullet> (nmultf xs a) = nmultf (p \<bullet> xs) (p \<bullet> a)"
proof(induct xs arbitrary: a p)
  case Nil then show ?case by simp
next
  case (Cons x xs a p)
  then show ?case
    apply(simp, subst freshbind)
    apply(rule supports_finite[of "supp (x, xs, a)"])
    apply(auto simp: supp_args)
  done
qed

(* hide the FRESH-based simps using a def and new lemmas *)
definition "nmult = nmultf"

lemma nmult_eqvt[eqvt]: "p \<bullet> (nmult xs a) = nmult (p \<bullet> xs) (p \<bullet> a)"
by(auto simp:nmult_def)

lemma nmult_nil [simp]:
  shows "nmult [] a = u<a>"
unfolding nmult_def by auto

lemma nmult_step[intro]:
  assumes "atom n \<sharp> (x,xs,a)"
  shows "nmult (x#xs) a = (bnd n . m<x, n><a> \<cdot> nmult xs n)"
apply(simp add:nmult_def)
apply(subst Fresh_apply'[of n])
apply(subst supports_fresh[of "supp (x, xs, a)"])
apply(auto simp:assms supp_args)
apply(metis permute_self permute_swap_cancel swap_eqvt)
done

lemma nmult_fresh[simp]:
  assumes "at \<sharp> (xs,a)"
  shows "at \<sharp> nmult xs a"
by(auto simp:fresh_fun_app assms)

lemma nmult_assoc1:
  assumes "atom n \<sharp> (y, z, xs, a)"
  shows "bnd n . m<y,n><a> \<cdot> nmult (z # xs) n \<approx> bnd n . m<y,z><n> \<cdot> nmult (n # xs) a"
proof -
  def [simp]: ctx \<equiv> "(y,z,xs,a)"
  (* define some temporary fresh names for the calculation *)
  note fr = assms
  obtain n1::name where "atom n1 \<sharp> ctx" by (rule obtain_fresh) note fr = this fr
  obtain n2::name where "atom n2 \<sharp> (ctx,n1)" by (rule obtain_fresh) note fr = this fr
  have "atom n1 \<sharp> n2" by (simp only:fr fresh_symm) note fr = this fr
  note [simp] = fr[simplified]

  (* all steps solvable with
     using tens_ac by (auto?, blast?, ((rule tens_subs, auto?)+)?)
   *)

  (* \<alpha>-convert (not technically necessary, mainly here for demonstration) *)
  have "bnd n . m<y,n><a> \<cdot> nmult (z # xs) n \<approx> bnd n1 . m<y, n1><a> \<cdot> nmult (z # xs) n1"
  by qstep
  
  (* unfold nmult *)
  also have "... \<approx> bnd n1 . bnd n2 . m<y, n1><a> \<cdot> m<z, n2><n1> \<cdot> nmult xs n2"
  using nmult_step[of n2] by qstep

  (* tensor axioms *)
  also have "... \<approx> bnd n1 . bnd n2 . nmult xs n2 \<cdot> m<y, n1><a> \<cdot> m<z, n2><n1>" using tens_ac by qstep
  also have "... \<approx> bnd n2 . bnd n1 . nmult xs n2 \<cdot> m<y, n1><a> \<cdot> m<z, n2><n1>" by qstep
  also have "... \<approx> bnd n2 . nmult xs n2 \<cdot> (bnd n1 . m<y, n1><a> \<cdot> m<z, n2><n1>)" by qstep

  (* apply associativity of 'm' *)
  also have "... \<approx> bnd n2 . nmult xs n2 \<cdot> (bnd n1 . m<n1,n2><a> \<cdot> m<y, z><n1>)" by qstep

  (* tensor axioms *)
  also have "... \<approx> bnd n2 . bnd n1 . nmult xs n2 \<cdot> m<n1,n2><a> \<cdot> m<y, z><n1>" by qstep
  also have "... \<approx> bnd n1 . bnd n2 . nmult xs n2 \<cdot> m<n1,n2><a> \<cdot> m<y, z><n1>" by qstep
  also have "... \<approx> bnd n1 . bnd n2 . m<y, z><n1> \<cdot> m<n1,n2><a> \<cdot> nmult xs n2" using tens_ac by qstep
  also have "... \<approx> bnd n1 . m<y, z><n1> \<cdot> (bnd n2 . m<n1,n2><a> \<cdot> nmult xs n2)" by qstep

  (* re-fold nmult *)
  also have "... \<approx> bnd n1 . m<y, z><n1> \<cdot> nmult (n1 # xs) a"
  using nmult_step[of n2] by qstep

  (* \<alpha>-convert to remove temporary names *)
  also have "... \<approx> bnd n . m<y, z><n> \<cdot> nmult (n # xs) a" by qstep

  finally show ?thesis .
qed

lemma nmult_unit1[simp]:
  assumes "atom a \<sharp> xs"
  assumes "atom n \<sharp> (a,xs)"
  shows "bnd n . u<n> \<cdot> nmult (n # xs) a \<approx> nmult xs a"
proof -
  note fr = assms
  obtain n1::name where "atom n1 \<sharp> (xs,a,n)" by (rule obtain_fresh) note fr = this fr
  have "atom n \<sharp> n1" by (simp only:fresh_symm fr) note fr = this fr
  have "atom a \<sharp> n1" by (simp only:fresh_symm fr) note fr = this fr
  note [simp] = fr[simplified]

  have "bnd n . u<n> \<cdot> nmult (n # xs) a \<approx> bnd n . u<n> \<cdot> (bnd n1 . m<n, n1><a> \<cdot> nmult xs n1)"
  using nmult_step[of n1] by auto

  also have "... \<approx> bnd n . bnd n1 . u<n> \<cdot> m<n, n1><a> \<cdot> nmult xs n1" by qstep
  also have "... \<approx> bnd n1 . bnd n . u<n> \<cdot> m<n, n1><a> \<cdot> nmult xs n1" by qstep
  also have "... \<approx> bnd n1 . (bnd n . u<n> \<cdot> m<n, n1><a>) \<cdot> nmult xs n1" by qstep
  also have "... \<approx> bnd n1 . id<a><n1> \<cdot> nmult xs n1" by qstep
  also have "... \<approx> (a \<leftrightarrow> n1) \<bullet> nmult xs n1" by qstep
  also have "... \<approx> nmult xs a" by qstep
  finally show ?thesis .
qed

theorem nmult_assoc:
  shows   "atom a \<sharp> (xs, ys) \<Longrightarrow> atom n \<sharp> (xs, ys, a) \<Longrightarrow>
           bnd n . nmult xs n \<cdot> nmult (n # ys) a \<approx> nmult (xs @ ys) a"
proof(induct xs arbitrary:n a)
case Nil
  then show ?case by simp (* uses lemma nmult_unit1 *)
next
case (Cons z zs n a)
  note ih = this
  note fr = assms
  obtain n1::name where "atom n1 \<sharp> (z,zs,ys,a,n)" by (rule obtain_fresh) note fr = this fr
  have "atom n \<sharp> (n1,z,zs)" using fr ih by (simp only:fresh_symm fr newfresh, blast) note fr = this fr
  have "atom a \<sharp> n1" by (simp only:fresh_symm fr) note fr = this fr
  note [simp] = fr ih

  (* unroll nmult *)
  have "bnd n . nmult (z # zs) n \<cdot> nmult (n # ys) a \<approx>
         bnd n . (bnd n1 . nmult zs n1 \<cdot> m<z,n1><n>) \<cdot> nmult (n # ys) a"
  using nmult_step[of n1] by qstep

  (* tensor axioms *)
  also have "... \<approx> bnd n . bnd n1 . nmult zs n1 \<cdot> m<z,n1><n> \<cdot> nmult (n # ys) a" by qstep
  also have "... \<approx> bnd n1 . bnd n . nmult zs n1 \<cdot> m<z,n1><n> \<cdot> nmult (n # ys) a" by qstep
  also have "... \<approx> bnd n1 . nmult zs n1 \<cdot> (bnd n . m<z,n1><n> \<cdot> nmult (n # ys) a)" by qstep

  (* apply lemma nmult_assoc1 *)
  also have "... \<approx> bnd n1 . nmult zs n1 \<cdot> (bnd n . m<z,n><a> \<cdot> nmult (n1 # ys) n)"
  using nmult_assoc1[of n] by qstep

  (* tensor axioms *)
  also have "... \<approx> bnd n1 . bnd n . nmult zs n1 \<cdot> m<z,n><a> \<cdot> nmult (n1 # ys) n" by qstep
  also have "... \<approx> bnd n1 . bnd n . m<z,n><a> \<cdot> nmult zs n1 \<cdot> nmult (n1 # ys) n" by qstep
  also have "... \<approx> bnd n . bnd n1 . m<z,n><a> \<cdot> nmult zs n1 \<cdot> nmult (n1 # ys) n" by qstep
  also have "... \<approx> bnd n . m<z,n><a> \<cdot> (bnd n1 . nmult zs n1 \<cdot> nmult (n1 # ys) n)" by qstep

  (* apply IH *)
  also have "... \<approx> bnd n . m<z,n><a> \<cdot> nmult (zs @ ys) n" by qstep

  (* re-roll nmult *)
  also have "... \<approx> nmult ((z # zs) @ ys) a"
  using nmult_step[of n] by qstep

  finally show ?case .
qed

end
