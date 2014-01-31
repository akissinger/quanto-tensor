theory RecursiveTest
imports "TensorMonoid"
begin

primrec nmult :: "name list \<Rightarrow> name \<Rightarrow> monoid"
where
  "nmult [] a = u<a>"
| "nmult (x # xs) a = (FRESH y . bnd y . m<x, y><a> \<cdot> nmult xs y)"

lemma nmult_eqvt[eqvt]:
  shows "p \<bullet> (nmult xs a) = nmult (p \<bullet> xs) (p \<bullet> a)"
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

declare nmult.simps(2)[simp del]

lemma nmult_step[intro]:
  assumes "atom n \<sharp> (x,xs,a)"
  shows "nmult (x#xs) a = (bnd n . m<x, n><a> \<cdot> nmult xs n)"
apply(simp add:nmult.simps(2))
apply(subst Fresh_apply'[of n])
apply(subst supports_fresh[of "supp (x, xs, a)"])
apply(auto simp:assms supp_args)
by (metis permute_self permute_swap_cancel swap_eqvt)

lemma nmult_fresh[simp]:
  assumes "at \<sharp> (xs,a)"
  shows "at \<sharp> nmult xs a"
by(auto simp:fresh_fun_app assms)

lemma nmult_assoc1:
  assumes [fr]:"atom n \<sharp> (y, z, xs, a)"
  shows "bnd n . m<y,n><a> \<cdot> nmult (z # xs) n \<approx> bnd n . m<y,z><n> \<cdot> nmult (n # xs) a"
proof -
  (* define some temporary fresh names for the calculation *)
  obtain n1::name where [fr]:"atom n1 \<sharp> (y,z,xs,a)" by (rule obtain_fresh)
  obtain n2::name where [fr]:"atom n2 \<sharp> (y,z,xs,a,n1)" by (rule obtain_fresh)
  have [fr]:"atom n1 \<sharp> n2" by (simp only:fr fresh_symm)

  (* \<alpha>-convert (not technically necessary, mainly here for demonstration) *)
  have "bnd n . m<y,n><a> \<cdot> nmult (z # xs) n \<approx> bnd n1 . m<y, n1><a> \<cdot> nmult (z # xs) n1"
  by qstep
  
  (* unfold nmult *)
  also have "... \<approx> bnd n1 . bnd n2 . m<y, n1><a> \<cdot> m<z, n2><n1> \<cdot> nmult xs n2"
  by (qstep simp:nmult_step[of n2])

  (* tensor axioms *)
  also have "... \<approx> bnd n1 . bnd n2 . nmult xs n2 \<cdot> m<y, n1><a> \<cdot> m<z, n2><n1>" by qstep
  also have "... \<approx> bnd n2 . bnd n1 . nmult xs n2 \<cdot> m<y, n1><a> \<cdot> m<z, n2><n1>" by qstep
  also have "... \<approx> bnd n2 . nmult xs n2 \<cdot> (bnd n1 . m<y, n1><a> \<cdot> m<z, n2><n1>)" by qstep

  (* apply associativity of 'm' *)
  also have "... \<approx> bnd n2 . nmult xs n2 \<cdot> (bnd n1 . m<n1,n2><a> \<cdot> m<y, z><n1>)" by qstep

  (* tensor axioms *)
  also have "... \<approx> bnd n2 . bnd n1 . nmult xs n2 \<cdot> m<n1,n2><a> \<cdot> m<y, z><n1>" by qstep
  also have "... \<approx> bnd n1 . bnd n2 . nmult xs n2 \<cdot> m<n1,n2><a> \<cdot> m<y, z><n1>" by qstep
  also have "... \<approx> bnd n1 . bnd n2 . m<y, z><n1> \<cdot> m<n1,n2><a> \<cdot> nmult xs n2" by qstep
  also have "... \<approx> bnd n1 . m<y, z><n1> \<cdot> (bnd n2 . m<n1,n2><a> \<cdot> nmult xs n2)" by qstep

  (* re-fold nmult *)
  also have "... \<approx> bnd n1 . m<y, z><n1> \<cdot> nmult (n1 # xs) a"
  by (qstep simp:nmult_step[of n2])

  (* \<alpha>-convert to remove temporary names *)
  also have "... \<approx> bnd n . m<y, z><n> \<cdot> nmult (n # xs) a" by qstep

  finally show ?thesis .
qed

lemma nmult_unit1[simp]:
  assumes [fr]:"atom a \<sharp> xs"
  assumes [fr]:"atom n \<sharp> (a,xs)"
  shows "bnd n . u<n> \<cdot> nmult (n # xs) a \<approx> nmult xs a"
proof -
  note [fr] = assms
  obtain n1::name where [fr]: "atom n1 \<sharp> (xs,a,n)" by (rule obtain_fresh)
  have [fr]:"atom n \<sharp> n1" by (simp only:fresh_symm fr)
  have [fr]:"atom a \<sharp> n1" by (simp only:fresh_symm fr)

  have "bnd n . u<n> \<cdot> nmult (n # xs) a \<approx> bnd n . u<n> \<cdot> (bnd n1 . m<n, n1><a> \<cdot> nmult xs n1)"
  using nmult_step[of n1] by qstep

  also have "... \<approx> bnd n . bnd n1 . u<n> \<cdot> m<n, n1><a> \<cdot> nmult xs n1" by qstep
  also have "... \<approx> bnd n1 . bnd n . u<n> \<cdot> m<n, n1><a> \<cdot> nmult xs n1" by qstep
  also have "... \<approx> bnd n1 . (bnd n . u<n> \<cdot> m<n, n1><a>) \<cdot> nmult xs n1" by qstep
  also have "... \<approx> bnd n1 .  nmult xs n1 \<cdot> id<n1><a>" by qstep
  also have "... \<approx> (n1 \<leftrightarrow> a) \<bullet> nmult xs n1" by qstep
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
  note ih[simp] = this
  note [fr] = assms
  obtain n1::name where [fr]:"atom n1 \<sharp> (z,zs,ys,a,n)" by (rule obtain_fresh)
  have [fr]:"atom n \<sharp> (n1,z,zs)" using ih by (simp only:fresh_symm fr newfresh, blast)
  have [fr]:"atom a \<sharp> n1" by (simp only:fresh_symm fr)

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
