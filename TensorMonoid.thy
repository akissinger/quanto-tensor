theory TensorMonoid
imports "../Nominal/Nominal2"
begin

atom_decl name

nominal_datatype monoid =
  COMBINE "monoid" "monoid" (infixr "\<cdot>" 150)
| BIND "x"::name "t"::monoid binds x in t ("bnd _ . _" [100,100] 100)
| ID "name" "name" ("id<_><_>" [200,200] 200)
| MULT "name" "name" "name" ("m<_, _><_>" [200,200,200] 200)
| UNIT "name" ("u<_>" [200] 200)

lemma fresh_symm:
  assumes "atom (a::name) \<sharp> (b::name)"
  shows "atom b \<sharp> a"
using assms
by simp

theorems newfresh = fresh_Nil fresh_Pair fresh_Cons swap_fresh_fresh flip_def fresh_append

inductive
  tens_eq :: "monoid \<Rightarrow> monoid \<Rightarrow> bool" (infix "\<approx>" 50)
where
  tens_eq_refl[intro]: "s = t \<Longrightarrow> s \<approx> t"
| tens_eq_trans[intro,trans]: "s \<approx> t \<Longrightarrow> t \<approx> u \<Longrightarrow> s \<approx> u"
| tens_eq_sym[intro]: "s \<approx> t \<Longrightarrow> t \<approx> s"
| tens_comm[simp]: "s \<cdot> t \<approx> t \<cdot> s"
| tens_assoc[simp]: "(s \<cdot> t) \<cdot> u \<approx> s \<cdot> t \<cdot> u"
| tens_dist[simp]: "atom a \<sharp> s \<Longrightarrow> s \<cdot> (bnd a . t) \<approx> bnd a . s \<cdot> t"
| tens_bnd_swap[intro]: "a \<noteq> b \<Longrightarrow> bnd a . bnd b . s \<approx> bnd b . bnd a . s"
| tens_pr_sub[intro]: "s \<approx> t \<Longrightarrow> u \<cdot> s \<approx> u \<cdot> t"
| tens_bnd_sub[intro]: "s \<approx> t \<Longrightarrow> bnd a . s \<approx> bnd a . t"
| id_pre[intro]: "atom a \<sharp> s \<Longrightarrow> bnd b . id<a><b> \<cdot> s \<approx> (a \<leftrightarrow> b) \<bullet> s"
| id_post[intro]: "atom b \<sharp> s \<Longrightarrow> bnd a . s \<cdot> id<a><b> \<approx> (a \<leftrightarrow> b) \<bullet> s"
| mult_assoc[intro]:
    "bnd x . m<x,c><d> \<cdot> m<a,b><x> \<approx>
     bnd x. m<a,x><d> \<cdot> m<b,c><x>"
| mult_unit[intro]:
    "bnd x . u<x> \<cdot> m<x, b><a> \<approx> id<a><b>"

find_theorems "?\<pi> \<bullet> (?a \<leftrightarrow> ?b) \<bullet> ?sa"

lemma permute_flip:
  "\<pi> \<bullet> (a \<leftrightarrow> b) \<bullet> s = (\<pi> \<bullet> a \<leftrightarrow> \<pi> \<bullet> b) \<bullet> \<pi> \<bullet> s"
by (metis flip_eqvt permute_eqvt)

lemma tens_eq_eqvt[eqvt]: "s \<approx> t \<Longrightarrow> \<pi> \<bullet> s \<approx> \<pi> \<bullet> t"
by (rule tens_eq.induct [of s t],auto simp:permute_flip)


(*nominal_inductive tens_eq
done*)

lemma tens_pr_sub_left[intro]:
  shows "s \<approx> t \<Longrightarrow> s \<cdot> u \<approx> t \<cdot> u"
using tens_pr_sub tens_comm by(blast)

theorems tens_subs = tens_pr_sub tens_pr_sub_left tens_bnd_sub
theorems tens_ac = tens_assoc tens_comm

(* distributivity helpers *)
lemma tens_dist_left[simp]:
  "atom a \<sharp> t \<Longrightarrow> (bnd a . s) \<cdot> t \<approx> bnd a . s \<cdot> t"
using tens_dist tens_comm by(blast)

lemma tens_dist3[simp]:
  "atom a \<sharp> u \<Longrightarrow> (bnd a . s \<cdot> t) \<cdot> u \<approx> bnd a . s \<cdot> t \<cdot> u"
using tens_dist tens_comm tens_assoc by (blast)

lemma freshbind:
  assumes fin: "finite (supp f)"
  shows "p \<bullet> (FRESH y . bnd y . (f y)) = (FRESH y . bnd y. ((p \<bullet> f) y))"
proof -
have "(supp f) supports (\<lambda>y. bnd y . f y)"
  by (auto simp add:supports_def swap_fresh_fresh fresh_def)
then have fin1: "finite (supp (\<lambda>y. bnd y . f y))"
  by (simp add: finite_supp fin supports_finite)
obtain c :: name where "atom c \<sharp> (\<lambda>y. bnd y . f y)"
  using fin1 by (rule_tac obtain_fresh')
hence fr: "atom c \<sharp> (\<lambda>y. bnd y . f y, bnd c . f c)" by(simp add:fresh_Pair)

show ?thesis
  apply(subst Fresh_eqvt)
  apply(rule exI[where x = c])
  apply(simp_all add:fresh_Pair fr)
done
qed

theorems supp_args = supports_def permute_fun_def fresh_def[symmetric] swap_fresh_fresh finite_supp

text {* A fairly crude first approximation of a tactic that solves most single proof steps *}

ML {*
signature S = SIMPLIFIER
  (* qstep_tac -- a tactic for solving fairly trivial tensor equations *)
  fun qstep_tac ctxt =
    let
      val gen_ctxt =
        ctxt
         |> Simplifier.map_simpset (
              fold Splitter.add_split @{thms prod.splits} #>
              fold Simplifier.add_simp @{thms split_def tens_subs newfresh})
      (* blast is used to solve equations up to AC. temporarily tag these rules as intro! *)
      val blast_ctxt = Classical.addSIs (gen_ctxt, @{thms tens_comm tens_assoc})
    in (
         (* optionally deal with renamings due to "id" contactions, then hit the goal with auto *)
         SOLVED' (K (
           TRY (rtac @{thm id_pre} 1) THEN
           TRY (rtac @{thm id_post} 1) THEN
           auto_tac gen_ctxt)
         ) 1 ORELSE
         (* deal with AC equations, using blast *)
         blast_tac blast_ctxt 1 ORELSE
         (* burrow down to differig sub-expression using "rule", then hit with auto *)
         REPEAT((rtac @{thm tens_pr_sub} 1 ORELSE rtac @{thm tens_bnd_sub} 1)
                THEN TRY(auto_tac gen_ctxt))
       )
    end
*}

method_setup qstep = {*
  (*concrete syntax like "clarsimp", "auto" etc.*)
  Method.sections Clasimp.clasimp_modifiers >>
    (*Isar method boilerplate*)
    (fn _ => fn ctxt => SIMPLE_METHOD (CHANGED (qstep_tac ctxt)))  
*}

notepad
begin
fix x y :: name
have "bnd x . id<x><x> \<approx> bnd y . id<y><y>"
apply(qstep)
done
end

end
