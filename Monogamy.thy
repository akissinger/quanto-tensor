theory Monogamy
imports "TensorMonoid"
begin

text {*
This file defines well-formed tensor expressions. For an expression to be well-formed, it needs
to be
 (a) monogamous - all names occur at most once in the up- and down-support
 (b) closed - all matched pairs of names should be bound
*}

nominal_primrec (invariant "\<lambda>x (y::atom set). finite y")
usupp :: "monoid \<Rightarrow> atom set"
where
  "usupp (s \<cdot> t) = usupp s \<union> usupp t"
| "usupp (bnd x . s) = usupp s - {atom x}"
| "usupp (id<a><b>) = {atom b}"
| "usupp (m<a,b><c>) = {atom c}"
| "usupp (u<a>) = {atom a}"
apply(simp_all add:eqvt_def usupp_graph_aux_def)
apply(erule usupp_graph.induct,auto)[]
apply(metis monoid.exhaust)
apply(simp only:Abs1_eq_iff_all(3)[symmetric])
apply(erule Abs_lst1_fcb2[where c="()"],
      auto simp: fresh_star_def eqvt_at_def fresh_Unit)[]
apply(simp add:Diff_eqvt fresh_minus_atom_set)
done

termination (eqvt) 
  by lexicographic_order

nominal_primrec (invariant "\<lambda>x (y::atom set). finite y")
dsupp :: "monoid \<Rightarrow> atom set"
where
  "dsupp (s \<cdot> t) = dsupp s \<union> dsupp t"
| "dsupp (bnd x . s) = dsupp s - {atom x}"
| "dsupp (id<a><b>) = {atom a}"
| "dsupp (m<a,b><c>) = {atom a, atom b}"
| "dsupp (u<a>) = {}"
(*using [[simproc del: alpha_lst]]*)
apply(simp_all add:eqvt_def dsupp_graph_aux_def)
apply(erule dsupp_graph.induct,auto)[]
apply(metis monoid.exhaust)
apply(simp only:Abs1_eq_iff_all(3)[symmetric])
apply(erule Abs_lst1_fcb2[where c="()"],
      auto simp: fresh_star_def eqvt_at_def fresh_Unit)[]
apply(simp add:Diff_eqvt fresh_minus_atom_set)
done

termination (eqvt) 
  by lexicographic_order

text {* Monogamy predicate *}

inductive
  mng :: "monoid \<Rightarrow> bool"
where
  id_mng[simp]: "mng (id<a><b>)"
| m_mng[simp]: "a \<noteq> b \<Longrightarrow> mng (m<a,b><c>)"
| u_mng[simp]: "mng (u<a>)"
| prod_mng[intro]: "dsupp s \<sharp>* dsupp t \<Longrightarrow> usupp s \<sharp>* usupp t \<Longrightarrow> mng s \<Longrightarrow> mng t \<Longrightarrow> mng (s \<cdot> t)"
| bnd_mng[intro]: "atom a \<in> dsupp s \<Longrightarrow> atom a \<in> usupp s \<Longrightarrow> mng s \<Longrightarrow> mng (bnd a . s)"

theorem mng_eqvt[eqvt]: "mng s \<Longrightarrow> mng (\<pi> \<bullet> s)"
proof(induct rule:mng.induct [of s],auto)
  fix s t :: monoid
  fix \<pi> :: perm

  assume "dsupp s \<sharp>* dsupp t"
  hence "\<pi> \<bullet> (dsupp s \<sharp>* dsupp t)" by (rule permute_boolI)
  hence fr1: "dsupp (\<pi> \<bullet> s) \<sharp>* dsupp (\<pi> \<bullet> t)" by simp

  assume "usupp s \<sharp>* usupp t"
  hence "\<pi> \<bullet> (usupp s \<sharp>* usupp t)" by (rule permute_boolI)
  hence fr2: "usupp (\<pi> \<bullet> s) \<sharp>* usupp (\<pi> \<bullet> t)" by simp

  assume "mng (\<pi> \<bullet> s)" and "mng (\<pi> \<bullet> t)"
  thus "mng ((\<pi> \<bullet> s) \<cdot> (\<pi> \<bullet> t))" using fr1 fr2 by auto
next
  fix a :: name
  fix s :: monoid
  fix \<pi> :: perm

  assume "atom a \<in> dsupp s"
  hence "\<pi> \<bullet> (atom a \<in> dsupp s)" by (rule permute_boolI)
  hence s1: "atom (\<pi> \<bullet> a) \<in> dsupp (\<pi> \<bullet> s)" by simp

  assume "atom a \<in> usupp s"
  hence "\<pi> \<bullet> (atom a \<in> usupp s)" by (rule permute_boolI)
  hence s2: "atom (\<pi> \<bullet> a) \<in> usupp (\<pi> \<bullet> s)" by simp

  assume "mng (\<pi> \<bullet> s)"
  thus "mng (bnd (\<pi> \<bullet> a) . (\<pi> \<bullet> s))" using s1 s2 bnd_mng[of "\<pi> \<bullet> a"] by simp
qed

text {* Well-formed tensors are monogamous and closed *}

definition wft :: "monoid \<Rightarrow> bool"
where "wft t \<equiv> mng t \<and> (dsupp t \<sharp>* usupp t)"

lemma wft_eqvt[eqvt]:
  shows "wft t \<Longrightarrow> wft (\<pi> \<bullet> t)"
unfolding wft_def
proof(auto simp:mng_eqvt)
assume "dsupp t \<sharp>* usupp t"
hence "\<pi> \<bullet> (dsupp t \<sharp>* usupp t)" by (rule permute_boolI)
thus "dsupp (\<pi> \<bullet> t) \<sharp>* usupp (\<pi> \<bullet> t)" by simp
qed

end
