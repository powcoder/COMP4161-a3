theory a3_pt2

imports AutoCorres.AutoCorres
  "a3_pt1"

begin


install_C_file "heap.c"

find_theorems "heap_global_addresses.set_top_body"


autocorres [ts_rules = pure nondet] "heap.c"


context heap begin

find_theorems "set_top'"


type_synonym th_dom = "(tree_heap_C ptr \<Rightarrow> bool)"
type_synonym th_vals = "(tree_heap_C ptr \<Rightarrow> tree_heap_C)"

lemma tree_heap_C_eq:
  fixes struct1 :: tree_heap_C
    and struct2 :: tree_heap_C
  shows "(struct1 = struct2) = (delay_C struct1 = delay_C struct2 \<and>
    left_C struct1 = left_C struct2 \<and>
    right_C struct1 = right_C struct2 \<and>
    data_C struct1 = data_C struct2)"
  sorry (* TODO: Q2.1: prove this *)


text \<open>
This inductive predicate captures the cases where a finite tree
exists starting at a particular pointer. This excludes cases where
the pointer structure would loop and the encoded tree would be
infinite.
\<close>

inductive tree_in_C :: "th_dom \<Rightarrow> th_vals \<Rightarrow> tree_heap_C ptr \<Rightarrow> bool"
  where
    tree_in_C_NULL:
    "tree_in_C th_dom th_vals NULL"
  | tree_in_C_Node:
    "p \<noteq> NULL \<Longrightarrow> th_dom p \<Longrightarrow>
    tree_in_C th_dom th_vals (left_C (th_vals p)) \<Longrightarrow>
    tree_in_C th_dom th_vals (right_C (th_vals p)) \<Longrightarrow>
    tree_in_C th_dom th_vals p"

inductive_simps tree_in_C_NULL_eq[simp]: "tree_in_C th_dom th_vals NULL"

lemma tree_in_C_not_NULL_eq:
  "p \<noteq> NULL \<Longrightarrow>
  tree_in_C th_dom th_vals p =
    (th_dom p \<and> tree_in_C th_dom th_vals (left_C (th_vals p)) \<and>
        tree_in_C th_dom th_vals (right_C (th_vals p)))"
  by (auto intro: tree_in_C_Node elim: tree_in_C.cases)

text \<open>
This function fetches the tree datatype, assuming there is a finite
tree present.
\<close>

function get_tree :: "th_dom \<Rightarrow> th_vals \<Rightarrow> tree_heap_C ptr \<Rightarrow>
    (tree_heap_C ptr \<times> word32 \<times> unit ptr) tree"
  where
    "get_tree th_dom th_vals NULL = Empty"
  | "p \<noteq> NULL \<Longrightarrow>
    get_tree th_dom th_vals p = (if tree_in_C th_dom th_vals p
    then Node (p, delay_C (th_vals p), data_C (th_vals p))
        (get_tree th_dom th_vals (left_C (th_vals p)))
        (get_tree th_dom th_vals (right_C (th_vals p)))
    else Empty)"
  by auto auto

text \<open>
The termination proof for @{term get_tree} makes use of the induction
principle given by the @{term tree_in_C} predicate. You don't have to
understand this termination proof in detail.
\<close>

termination get_tree
proof clarsimp
  fix th_dom th_vals p
  let ?P="Wellfounded.accp get_tree_rel (th_dom, th_vals, p)"
  have "tree_in_C th_dom th_vals p \<Longrightarrow> ?P"
    apply (induct rule: tree_in_C.induct)
     apply (rule accpI)
     apply (erule get_tree_rel.cases, simp_all)
    apply (rule accpI)
    apply (erule get_tree_rel.cases, simp_all)
    done
  also have "\<not> tree_in_C th_dom th_vals p \<Longrightarrow> ?P"
    apply (rule accpI)
    apply (erule get_tree_rel.cases)
     apply simp_all
    done
  ultimately show "?P"
    by auto
qed

text \<open>
Some state changes are irrelevant to the pointer structure of tree-heaps.
\<close>

lemma tree_in_C_fun_upd_unchanged_imp:
  "tree_in_C th_dom th_vals p \<Longrightarrow>
    left_C v = left_C (th_vals x) \<Longrightarrow>
    right_C v = right_C (th_vals x) \<Longrightarrow>
    tree_in_C th_dom (th_vals(x := v)) p"
  sorry (* TODO: Q2.2: prove this *)

text \<open>
We add syntax abbreviations to apply @{term tree_in_C} and @{term get_tree}
to the AutoCorres state type, which is called @{typ lifted_globals}.
\<close>

abbreviation
  tree_in_C_st :: "lifted_globals \<Rightarrow> tree_heap_C ptr \<Rightarrow> bool"
  where
  "tree_in_C_st s ptr \<equiv> tree_in_C (is_valid_tree_heap_C s) (heap_tree_heap_C s) ptr"

abbreviation
  get_tree_st :: "lifted_globals \<Rightarrow> tree_heap_C ptr \<Rightarrow> (tree_heap_C ptr \<times> 32 word \<times> unit ptr) tree"
  where
  "get_tree_st s ptr \<equiv> get_tree (is_valid_tree_heap_C s) (heap_tree_heap_C s) ptr"

text \<open>
The @{term set_top'} function is safe to execute, and doesn't change the
existence of a tree-heap at some other pointer.
\<close>
lemma set_top_tree_in_C_safe:
  "\<lbrace>\<lambda>s. tree_in_C_st s p2 \<and> ptr \<noteq> NULL \<and> tree_in_C_st s ptr\<rbrace>
    set_top' ptr th_dom th_vals
  \<lbrace>\<lambda>_ s. tree_in_C_st s p2\<rbrace>!"
  sorry (* TODO: Q2.3: prove this *)


text \<open>
The @{term min_delay'} function is safe to execute also. It doesn't change
the state, which means we know how to establish any postcondition @{term Q}
by showing it also holds at the input state. You will need to add additional
assumptions about the state in the precondition, and for the next proof you
will need to provide information about the return value.
\<close>
lemma min_delay_safe:
  "\<lbrace>\<lambda>s. FIXME_fact_about_input_state s \<and> (\<forall>min_rv. FIXME_info min_rv \<longrightarrow> Q min_rv s)\<rbrace>
   min_delay' p delay p2 p3
  \<lbrace>\<lambda>rv s. Q rv s\<rbrace>!"
  sorry (* TODO: Q2.4: adjust the precondition and prove the adjusted statement *)


text \<open>
Prove that the @{term push_down'} function is safe to execute as well.
This is a bigger function, and the proof might require a bit of work.

Because @{term push_down'} contains a loop and we are proving total correctness,
we must supply a termination relation. You can use the size of the tree reachable
from the current pointer @{term p2}.

You don't have to keep the skeleton proof here, but you do have to prove the
lemma as it is stated. However you prove it, you will probably need helper lemmas
about @{term get_tree}, @{term tree_in_C}, etc.

The skeleton proof here makes use of the above lemma about @{term min_delay'},
where you updated the precondition. If 
\<close>


lemma push_down_safe:
  "\<lbrace>\<lambda>st. tree_in_C_st st p \<and> p \<noteq> NULL\<rbrace>
    push_down' p delay data
  \<lbrace>\<lambda>rv st. tree_in_C_st st p\<rbrace>!"

  (* this proof skeleton is supplied as a helper. *)
  (* you can fill in the blanks, or replace the whole proof if you like. *)

  apply (simp add: push_down'_def set_top'_def)
  apply wp
   apply (rule_tac I="\<lambda>p2 st. FIXME_write_an_invariant p2 st"
        and R="measure (\<lambda>(p2, st). size (get_tree_st st p2))" in validNF_whileLoop)
      apply assumption
     apply wp
         apply (simp split del: if_split cong: if_cong)
         apply (wp min_delay_safe)
        apply wp+
     (* now you need to prove the main loop-invariant condition.
        this will only be possible if you gave a sufficiently weak (provable)
        precondition for min_delay_safe *)

  sorry (* TODO: Q2.5: prove the original statement,
        either using the above proof skeleton or otherwise *)


text \<open>
Finally, prove that the simple @{term set_top'} operation produces the
correct output tree.

To prove this, we need to use the fact that the tree pointers do not
include any sharing, so all the cells are at different addresses.
\<close>
lemma set_top_heap_is_heap_set_top:
  "\<lbrace>\<lambda>s. tree_in_C_st s ptr \<and> ptr \<noteq> NULL \<and>
            get_tree_st s ptr = v \<and>
            distinct (map fst (tree_elements (get_tree_st s ptr)))\<rbrace>
    set_top' ptr th_dom th_vals
  \<lbrace>\<lambda>_ s. get_tree_st s ptr = (tree_set_top v (ptr, th_dom, th_vals))\<rbrace>"
  sorry (* TODO: Q2.6: prove this *)

text \<open>
Congratulations, at this point you have done a bit of C verification!

A bigger task would be to prove that the @{term push_down'} operation produces
the correct output tree. You don't have to do that for this assignment. However,
if you are interested in trying it out, we've already built up all the concepts
you would need to try it.
\<close>


end
