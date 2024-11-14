theory a3_pt1

imports Main

begin


text \<open>
Part 1: Pure functions on tree-heaps.
\<close>

datatype 'a tree =
    Node "'a" "'a tree" "'a tree"
  | Empty





fun tree_elements :: "'a tree \<Rightarrow> 'a list"
  where
    "tree_elements Empty = []"
  | "tree_elements (Node x left right) =
    x # tree_elements left @ tree_elements right"


fun heap_tree_sorted :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a tree \<Rightarrow> bool"
  where
    "heap_tree_sorted ord Empty = True"
  | "heap_tree_sorted ord (Node x left right) =
    ((\<forall>y \<in> set (tree_elements left). ord x y) \<and>
        (\<forall>y \<in> set (tree_elements right). ord x y) \<and>
        heap_tree_sorted ord left \<and> heap_tree_sorted ord right)"


lemma heap_tree_sorted_implies_sorted:
  "sorted_wrt ord (tree_elements tree) \<Longrightarrow> heap_tree_sorted ord tree"
  sorry (* TODO: Q1.1: prove this *)


fun tree_top :: "'a tree \<Rightarrow> 'a"
  where
    "tree_top (Node x _ _) = x"

fun tree_set_top :: "'a tree \<Rightarrow> 'a \<Rightarrow> 'a tree"
  where
    "tree_set_top Empty _ = Empty"
  | "tree_set_top (Node _ left right) x = Node x left right"



fun heap_tree_push :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
  where
    "heap_tree_push ord x Empty = Empty"
  | "heap_tree_push ord x (Node _ left right) =
    (if left \<noteq> Empty \<and> ord (tree_top left) x \<and>
            (right = Empty \<or> ord (tree_top left) (tree_top right))
        then Node (tree_top left) (heap_tree_push ord x left) right
    else if right \<noteq> Empty \<and> ord (tree_top right) x
        then Node (tree_top right) left (heap_tree_push ord x right)
    else Node x left right)"



lemma heap_tree_push_same_structure:
  "rel_tree (\<lambda>_ _. True) hp (heap_tree_push ord x hp)"
  sorry (* TODO: Q2.2: prove this *)


lemma heap_tree_push_set_elements:
  "set (tree_elements (heap_tree_push ord x hp)) =
    set (tree_elements (tree_set_top hp x))"
  sorry (* TODO: Q1.3: prove this *)


lemma heap_tree_push_sorted:
  fixes f :: "'a \<Rightarrow> int"
  assumes sorted: "heap_tree_sorted ord hp"
   and ord_eq: "ord = (\<lambda>x y. f x \<le> f y)"
  shows "heap_tree_sorted ord (heap_tree_push ord x hp)"
  sorry (* TODO: Q1.4: prove this

You may find that this proof requires some care. The automatic tools tend to
generate a lot of cases and diverge. In particular, the simplifier can break
up the goal into excessively many similar parts when it uses the automatic split
rule "if_split".

This split rule can be disabled like this:

  apply (simp split del: if_split)

The same "split del: " argument can be supplied to clarsimp, auto, etc.

Case division can then be done explicitly by using cases, case_tac or similar,
or by applying a single step of this split rule like this:

  apply (split if_split)

*)

end
