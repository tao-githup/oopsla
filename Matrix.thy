(*  Title:      HOL/Matrix_LP/Matrix.thy
    Author:     Steven Obua
*)

theory Matrix
imports Main "~~/src/HOL/Library/Lattice_Algebras"   Complex
begin

type_synonym infmatrix = "nat ⇒ nat ⇒ real"
consts infinite::nat

definition nonzero_positions :: "(nat ⇒ nat ⇒ real) ⇒ (nat × nat) set" where
  "nonzero_positions A = {pos. A (fst pos) (snd pos) ~= 0}"

definition "matrix = {(f::(nat ⇒ nat ⇒ real)). finite (nonzero_positions f)∧
   ( (nonzero_positions f) ~={}⟶ Max (fst`(nonzero_positions f))<infinite∧Max (snd`(nonzero_positions f))<infinite )  }"

typedef  matrix = "matrix :: (nat ⇒ nat ⇒ real) set"
  unfolding matrix_def
proof
  show "(λj i. 0) ∈ {(f::(nat ⇒ nat ⇒ real)). finite (nonzero_positions f)∧
  ((nonzero_positions f) ~={}⟶Max (fst`(nonzero_positions f))<infinite∧Max (snd`(nonzero_positions f))<infinite    )   }"
    apply (simp add: nonzero_positions_def)
    done
qed

declare Rep_matrix_inverse[simp]

lemma finite_nonzero_positions : "finite (nonzero_positions (Rep_matrix A)) ∧
  ((nonzero_positions (Rep_matrix A)) ~={}⟶Max (fst`(nonzero_positions (Rep_matrix A)))<infinite∧Max (snd`(nonzero_positions (Rep_matrix A)))<infinite    )"
  apply(induct A)
  apply(simp add:Abs_matrix_inverse matrix_def)
  using Rep_matrix matrix_def by blast

definition nrows :: " matrix ⇒ nat" where
  "nrows A == if nonzero_positions(Rep_matrix A) = {} then 0 else Suc(Max ((image fst) (nonzero_positions (Rep_matrix A))))"

definition ncols :: " matrix ⇒ nat" where
  "ncols A == if nonzero_positions(Rep_matrix A) = {} then 0 else Suc(Max ((image snd) (nonzero_positions (Rep_matrix A))))"
lemma nrows_max[simp]:"nrows A≤infinite"
  apply(simp add:nrows_def)
using finite_nonzero_positions by fastforce
lemma ncols_max[simp]:"ncols A≤infinite"
apply(simp add:ncols_def)
using finite_nonzero_positions by fastforce
lemma nrows:
  assumes hyp: "nrows A ≤ m"
  shows "(Rep_matrix A m n) = 0"
proof cases
  assume "nonzero_positions(Rep_matrix A) = {}"
  then show "(Rep_matrix A m n) = 0" by (simp add: nonzero_positions_def)
next
  assume a: "nonzero_positions(Rep_matrix A) ≠ {}"
  let ?S = "fst`(nonzero_positions(Rep_matrix A))"
  have c: "finite (?S)" by (simp add: finite_nonzero_positions)
  from hyp have d: "Max (?S) < m" by (simp add: a nrows_def)
  have "m ∉ ?S" 
    proof -
      have "m ∈ ?S ⟹ m <= Max(?S)" by (simp add: Max_ge [OF c])
      moreover from d have "~(m <= Max ?S)" by (simp)
      ultimately show "m ∉ ?S" by (auto)
    qed
  then show "Rep_matrix A m n = 0" by (simp add: nonzero_positions_def image_Collect)
qed

definition transpose_infmatrix :: " infmatrix ⇒  infmatrix" where
  "transpose_infmatrix A j i == A i j"

definition transpose_matrix :: " matrix ⇒  matrix" where
  "transpose_matrix == Abs_matrix o transpose_infmatrix o Rep_matrix"

declare transpose_infmatrix_def[simp]
(*ext  (∀x. f x = g x) =⇒ f = g*)
lemma transpose_infmatrix_twice[simp]: "transpose_infmatrix (transpose_infmatrix A) = A"
by ((rule ext)+, simp)

lemma transpose_infmatrix: "transpose_infmatrix (% j i. P j i) = (% j i. P i j)"
  apply (rule ext)+
  by simp

lemma transpose_infmatrix_closed[simp]: "Rep_matrix (Abs_matrix (transpose_infmatrix (Rep_matrix x))) = transpose_infmatrix (Rep_matrix x)"
apply (rule Abs_matrix_inverse)
apply (simp add: matrix_def nonzero_positions_def image_def)
proof -
  let ?A = "{pos. Rep_matrix x (snd pos) (fst pos) ≠ 0}"
  let ?swap = "% pos. (snd pos, fst pos)"
  let ?B = "{pos. Rep_matrix x (fst pos) (snd pos) ≠ 0}"
  have swap_image: "?swap`?A = ?B"
    apply (simp add: image_def)
    apply (rule set_eqI)
    apply (simp)
    proof
      fix y
      assume hyp: "∃a b. Rep_matrix x b a ≠ 0 ∧ y = (b, a)"
      thus "Rep_matrix x (fst y) (snd y) ≠ 0"
        proof -
          from hyp obtain a b where "(Rep_matrix x b a ≠ 0 & y = (b,a))" by blast
          then show "Rep_matrix x (fst y) (snd y) ≠ 0" by (simp)
        qed
    next
      fix y
      assume hyp: "Rep_matrix x (fst y) (snd y) ≠ 0"
      show "∃ a b. (Rep_matrix x b a ≠ 0 & y = (b,a))"
        by (rule exI[of _ "snd y"], rule exI[of _ "fst y"]) (simp add: hyp)
    qed
  then have "finite (?swap`?A)"
    proof -
      have "finite (nonzero_positions (Rep_matrix x))" by (simp add: finite_nonzero_positions)
      then have "finite ?B" by (simp add: nonzero_positions_def)
      with swap_image show "finite (?swap`?A)" by (simp)
    qed
  moreover
  have "inj_on ?swap ?A" by (simp add: inj_on_def)
  have " finite {pos. Rep_matrix x (snd pos) (fst pos) ≠ 0} " 
 using `inj_on (λpos. (snd pos, fst pos)) {pos. Rep_matrix x (snd pos) (fst pos) ≠ 0}` calculation finite_imageD by blast
  have " ((∃a b. Rep_matrix x b a ≠ 0) ⟶ Max {y. ∃b. Rep_matrix x b y ≠ 0} < infinite 
         ∧ Max {y. ∃a. Rep_matrix x y a ≠ 0} < infinite)"
  proof -
      have " (nonzero_positions (Rep_matrix x)) ~={}⟶Max (fst`(nonzero_positions (Rep_matrix x)))<infinite
      ∧Max (snd`(nonzero_positions (Rep_matrix x)))<infinite"
     using finite_nonzero_positions by blast
     then have "((nonzero_positions (Rep_matrix x)) ~={}) = (∃a b. Rep_matrix x b a ≠ 0)"
     by (metis (mono_tags, lifting) Collect_empty_eq le0 nonzero_positions_def nrows nrows_def)
     then have " fst ` {pos. Rep_matrix x (fst pos) (snd pos) ≠ 0} = fst ` {(a,b). Rep_matrix x a b ≠ 0}"
    by (metis (mono_tags, lifting) Collect_cong split_beta')
    then have "fst ` {(a,b). Rep_matrix x a b ≠ 0} ={y. ∃a. Rep_matrix x y a ≠ 0}"
    apply(auto)
    by force
    then have "fst ` {pos. Rep_matrix x (fst pos) (snd pos) ≠ 0}={y. ∃a. Rep_matrix x y a ≠ 0}"
    by (simp add: `fst \` {pos. Rep_matrix x (fst pos) (snd pos) ≠ 0} = fst \` {(a, b). Rep_matrix x a b ≠ 0}`)
   
     then have " snd ` {pos. Rep_matrix x (fst pos) (snd pos) ≠ 0} = snd ` {(a,b). Rep_matrix x a b ≠ 0}"
    by (metis (mono_tags, lifting) Collect_cong split_beta')
    then have "snd ` {(a,b). Rep_matrix x a b ≠ 0} ={y. ∃b. Rep_matrix x b y ≠ 0}"
    apply(auto)
    by force
    then have "snd ` {pos. Rep_matrix x (fst pos) (snd pos) ≠ 0}= {y. ∃b. Rep_matrix x b y ≠ 0}"
    by (simp add: `snd \` {pos. Rep_matrix x (fst pos) (snd pos) ≠ 0} = snd \` {(a, b). Rep_matrix x a b ≠ 0}`)
     show " ((∃a b. Rep_matrix x b a ≠ 0) ⟶ Max {y. ∃b. Rep_matrix x b y ≠ 0} < infinite 
         ∧ Max {y. ∃a. Rep_matrix x y a ≠ 0} < infinite)"
   using `fst \` {pos. Rep_matrix x (fst pos) (snd pos) ≠ 0} = {y. ∃a. Rep_matrix x y a ≠ 0}` `nonzero_positions (Rep_matrix x) ≠ {} ⟶ Max (fst \` nonzero_positions (Rep_matrix x)) < infinite ∧ Max (snd \` nonzero_positions (Rep_matrix x)) < infinite` `snd \` {pos. Rep_matrix x (fst pos) (snd pos) ≠ 0} = {y. ∃b. Rep_matrix x b y ≠ 0}` nonzero_positions_def by auto
   qed
   then show " finite {pos. Rep_matrix x (snd pos) (fst pos) ≠ 0} ∧
    ((∃a b. Rep_matrix x b a ≠ 0) ⟶ Max {y. ∃b. Rep_matrix x b y ≠ 0} < infinite ∧ Max {y. ∃a. Rep_matrix x y a ≠ 0} < infinite)"
    using `finite {pos. Rep_matrix x (snd pos) (fst pos) ≠ 0}` by blast
qed

lemma infmatrixforward: "(x:: infmatrix) = y ⟹ ∀ a b. x a b = y a b" by auto

lemma transpose_infmatrix_inject: "(transpose_infmatrix A = transpose_infmatrix B) = (A = B)"
apply (auto)
apply (rule ext)+
apply (simp add: transpose_infmatrix)
apply (drule infmatrixforward)
apply (simp)
done

lemma transpose_matrix_inject: "(transpose_matrix A = transpose_matrix B) = (A = B)"
apply (simp add: transpose_matrix_def)
apply (subst Rep_matrix_inject[THEN sym])+
apply (simp only: transpose_infmatrix_closed transpose_infmatrix_inject)
done

lemma transpose_matrix[simp]: "Rep_matrix(transpose_matrix A) j i = Rep_matrix A i j"
by (simp add: transpose_matrix_def)

lemma transpose_transpose_id[simp]: "transpose_matrix (transpose_matrix A) = A"
by (simp add: transpose_matrix_def)

lemma nrows_transpose[simp]: "nrows (transpose_matrix A) = ncols A"
by (simp add: nrows_def ncols_def nonzero_positions_def transpose_matrix_def image_def)

lemma ncols_transpose[simp]: "ncols (transpose_matrix A) = nrows A"
by (simp add: nrows_def ncols_def nonzero_positions_def transpose_matrix_def image_def)

lemma ncols: "ncols A <= n ⟹ Rep_matrix A m n = 0"
proof -
  assume "ncols A <= n"
  then have "nrows (transpose_matrix A) <= n" by (simp)
  then have "Rep_matrix (transpose_matrix A) n m = 0" by (rule nrows)
  thus "Rep_matrix A m n = 0" by (simp add: transpose_matrix_def)
qed

lemma ncols_le: "(ncols A <= n) = (! j i. n <= i ⟶ (Rep_matrix A j i) = 0)" (is "_ = ?st")
apply (auto)
apply (simp add: ncols)
proof (simp add: ncols_def, auto)
  let ?P = "nonzero_positions (Rep_matrix A)"
  let ?p = "snd`?P"
  have a:"finite ?p" by (simp add: finite_nonzero_positions)
  let ?m = "Max ?p"
  assume "~(Suc (?m) <= n)"
  then have b:"n <= ?m" by (simp)
  fix a b
  assume "(a,b) ∈ ?P"
  then have "?p ≠ {}" by (auto)
  with a have "?m ∈  ?p" by (simp)
  moreover have "!x. (x ∈ ?p ⟶ (? y. (Rep_matrix A y x) ≠ 0))" by (simp add: nonzero_positions_def image_def)
  ultimately have "? y. (Rep_matrix A y ?m) ≠ 0" by (simp)
  moreover assume ?st
  ultimately show "False" using b by (simp)
qed

lemma less_ncols: "(n < ncols A) = (? j i. n <= i & (Rep_matrix A j i) ≠ 0)"
proof -
  have a: "!! (a::nat) b. (a < b) = (~(b <= a))" by arith
  show ?thesis by (simp add: a ncols_le)
qed

lemma le_ncols: "(n <= ncols A) = (∀ m. (∀ j i. m <= i ⟶ (Rep_matrix A j i) = 0) ⟶ n <= m)"
apply (auto)
apply (subgoal_tac "ncols A <= m")
apply (simp)
apply (simp add: ncols_le)
apply (drule_tac x="ncols A" in spec)
by (simp add: ncols)

lemma nrows_le: "(nrows A <= n) = (! j i. n <= j ⟶ (Rep_matrix A j i) = 0)" (is ?s)
proof -
  have "(nrows A <= n) = (ncols (transpose_matrix A) <= n)" by (simp)
  also have "… = (! j i. n <= i ⟶ (Rep_matrix (transpose_matrix A) j i = 0))" by (rule ncols_le)
  also have "… = (! j i. n <= i ⟶ (Rep_matrix A i j) = 0)" by (simp)
  finally show "(nrows A <= n) = (! j i. n <= j ⟶ (Rep_matrix A j i) = 0)" by (auto)
qed

lemma less_nrows: "(m < nrows A) = (? j i. m <= j & (Rep_matrix A j i) ≠ 0)"
proof -
  have a: "!! (a::nat) b. (a < b) = (~(b <= a))" by arith
  show ?thesis by (simp add: a nrows_le)
qed

lemma le_nrows: "(n <= nrows A) = (∀ m. (∀ j i. m <= j ⟶ (Rep_matrix A j i) = 0) ⟶ n <= m)"
apply (auto)
apply (subgoal_tac "nrows A <= m")
apply (simp)
apply (simp add: nrows_le)
apply (drule_tac x="nrows A" in spec)
by (simp add: nrows)

lemma nrows_notzero: "Rep_matrix A m n ≠ 0 ⟹ m < nrows A"
apply (case_tac "nrows A <= m")
apply (simp_all add: nrows)
done

lemma ncols_notzero: "Rep_matrix A m n ≠ 0 ⟹ n < ncols A"
apply (case_tac "ncols A <= n",auto)
apply (simp_all add: ncols)
done

lemma finite_natarray1: "finite {x. x < (n::nat)}"
apply (induct n)
apply (simp)
proof -
  fix n
  have "{x. x < Suc n} = insert n {x. x < n}"  by (rule set_eqI, simp, arith)
  moreover assume "finite {x. x < n}"
  ultimately show "finite {x. x < Suc n}" by (simp)
qed

lemma finite_natarray2: "finite {(x, y). x < (m::nat) & y < (n::nat)}"
by simp

lemma RepAbs_matrix:
  assumes aem: "? m<=infinite. ! j i. m <= j ⟶ x j i = 0" (is ?em) and aen:"? n<=infinite. ! j i. (n <= i ⟶ x j i = 0)" (is ?en)
  shows "(Rep_matrix (Abs_matrix x)) = x"
apply (rule Abs_matrix_inverse)
apply (simp add: matrix_def nonzero_positions_def)
proof -
  from aem obtain m where a: "! j i. m <= j ⟶ x j i = 0" by (blast)
  from aen obtain n where b: "! j i. n <= i ⟶ x j i = 0" by (blast)
  let ?u = "{(i, j). x i j ≠ 0}"
  let ?v = "{(i, j). i < m & j < n}"
  have c: "!! (m::nat) a. ~(m <= a) ⟹ a < m" by (arith)
  from a b have "(?u ∩ (-?v)) = {}"
    apply (simp)
    apply (rule set_eqI)
    apply (simp)
    apply auto
    by (rule c, auto)+
  then have d: "?u ⊆ ?v" by blast
  moreover have "finite ?v" by (simp add: finite_natarray2)
  moreover have "{pos. x (fst pos) (snd pos) ≠ 0} = ?u" by auto
  have "finite {pos. x (fst pos) (snd pos) ≠ 0}" 
  using `{pos. x (fst pos) (snd pos) ≠ 0} = {(i, j). x i j ≠ 0}` d finite_subset by fastforce
  have aa:"! j i. infinite <= j ⟶ x j i = 0" using aem by auto
  have bb:"! j i. infinite <= i ⟶ x j i = 0" using aen less_le_trans by auto
  have "fst ` {pos. x (fst pos) (snd pos) ≠ 0}= fst ` {(a,b).  x a b ≠ 0}"
  by (simp add: `{pos. x (fst pos) (snd pos) ≠ 0} = {(i, j). x i j ≠ 0}`)
  have " fst ` {(a,b).  x a b ≠ 0}={y. ∃a.  x y a ≠ 0}"
  apply auto
  by force
  have "fst ` {pos. x (fst pos) (snd pos) ≠ 0}={y. ∃a.  x y a ≠ 0}"
  by (simp add: `fst \` {(a, b). x a b ≠ 0} = {y. ∃a. x y a ≠ 0}` `fst \` {pos. x (fst pos) (snd pos) ≠ 0} = fst \` {(a, b). x a b ≠ 0}`)
  have a:"{y. ∃a. x y a ≠ 0}≠{}∧Max {y. ∃a. x y a ≠ 0} ≥ infinite ⟹ (∃ yy≥ infinite. yy∈{y. ∃a. x y a ≠ 0})"  
by (metis (no_types, lifting) Max_in `finite {pos. x (fst pos) (snd pos) ≠ 0}` `fst \` {(a, b). x a b ≠ 0} = {y. ∃a. x y a ≠ 0}` `{pos. x (fst pos) (snd pos) ≠ 0} = {(i, j). x i j ≠ 0}` finite_imageI)
  have "(∃a b. x a b ≠ 0) ⟶ Max ({y. ∃a.  x y a ≠ 0}) < infinite"
  apply auto
  using a aa c by blast
  have "snd ` {pos. x (fst pos) (snd pos) ≠ 0}= snd ` {(a,b).  x a b ≠ 0}"
   by (simp add: `{pos. x (fst pos) (snd pos) ≠ 0} = {(i, j). x i j ≠ 0}`)
   have " snd ` {(a,b).  x a b ≠ 0}={y. ∃a.  x a y ≠ 0}"
   apply auto
   by force
  have "(snd ` {pos. x (fst pos) (snd pos) ≠ 0}) = {y. ∃a.  x a y ≠ 0}"
 by (simp add: `snd \` {(a, b). x a b ≠ 0} = {y. ∃a. x a y ≠ 0}` `snd \` {pos. x (fst pos) (snd pos) ≠ 0} = snd \` {(a, b). x a b ≠ 0}`)
  have cc:" {y. ∃a. x a y ≠ 0}≠{}∧Max {y. ∃a. x a y ≠ 0} ≥ infinite ⟹ ? yy. yy≥infinite∧yy∈{y. ∃a. x a y ≠ 0}" sledgehammer
by (metis (no_types, lifting) Max_in `finite {pos. x (fst pos) (snd pos) ≠ 0}` `snd \` {(a, b). x a b ≠ 0} = {y. ∃a. x a y ≠ 0}` `{pos. x (fst pos) (snd pos) ≠ 0} = {(i, j). x i j ≠ 0}` finite_imageI)
 have "(∃a b. x a b ≠ 0) ⟶ Max ({y. ∃a.  x a y ≠ 0}) < infinite" 
using bb c cc by blast
 have " ((∃a b. x a b ≠ 0) ⟶ Max (fst ` {pos. x (fst pos) (snd pos) ≠ 0}) < infinite
         ∧ Max (snd ` {pos. x (fst pos) (snd pos) ≠ 0}) < infinite)"
by (simp add: `(∃a b. x a b ≠ 0) ⟶ Max {y. ∃a. x a y ≠ 0} < infinite` `(∃a b. x a b ≠ 0) ⟶ Max {y. ∃a. x y a ≠ 0} < infinite` `fst \` {pos. x (fst pos) (snd pos) ≠ 0} = {y. ∃a. x y a ≠ 0}` `snd \` {(a, b). x a b ≠ 0} = {y. ∃a. x a y ≠ 0}` `snd \` {pos. x (fst pos) (snd pos) ≠ 0} = snd \` {(a, b). x a b ≠ 0}`)
  ultimately show " finite {pos. x (fst pos) (snd pos) ≠ 0} ∧
    ((∃a b. x a b ≠ 0) ⟶ Max (fst ` {pos. x (fst pos) (snd pos) ≠ 0}) < infinite ∧ Max (snd ` {pos. x (fst pos) (snd pos) ≠ 0}) < infinite)"
  using `finite {pos. x (fst pos) (snd pos) ≠ 0}` by blast
qed


definition apply_infmatrix :: "(real ⇒ real) ⇒  infmatrix ⇒  infmatrix" where
  "apply_infmatrix f == % A. (% j i. f (A j i))"

definition apply_matrix :: "(real ⇒ real) ⇒  matrix ⇒  matrix" where
  "apply_matrix f == % A. Abs_matrix (apply_infmatrix f (Rep_matrix A))"

definition combine_infmatrix :: "(real ⇒ real ⇒ real) ⇒  infmatrix ⇒infmatrix ⇒infmatrix" where
  "combine_infmatrix f == % A B. (% j i. f (A j i) (B j i))"

definition combine_matrix :: "(real ⇒ real ⇒ real) ⇒matrix ⇒matrix ⇒ matrix" where
  "combine_matrix f == % A B. Abs_matrix (combine_infmatrix f (Rep_matrix A) (Rep_matrix B))"

lemma expand_apply_infmatrix[simp]: "apply_infmatrix f A j i = f (A j i)"
by (simp add: apply_infmatrix_def)

lemma expand_combine_infmatrix[simp]: "combine_infmatrix f A B j i = f (A j i) (B j i)"
by (simp add: combine_infmatrix_def)

definition commutative :: "('a ⇒ 'a ⇒ 'a) ⇒ bool" where
"commutative f == ! x y. f x y = f y x"

definition associative :: "('a ⇒ 'a ⇒ 'a) ⇒ bool" where
"associative f == ! x y z. f (f x y) z = f x (f y z)"

text{*
To reason about associativity and commutativity of operations on matrices,
let's take a step back and look at the general situtation: Assume that we have
sets $A$ and $B$ with $B \subset A$ and an abstraction $u: A \rightarrow B$. This abstraction has to fulfill $u(b) = b$ for all $b \in B$, but is arbitrary otherwise.
Each function $f: A \times A \rightarrow A$ now induces a function $f': B \times B \rightarrow B$ by $f' = u \circ f$.
It is obvious that commutativity of $f$ implies commutativity of $f'$: $f' x y = u (f x y) = u (f y x) = f' y x.$
*}

lemma combine_infmatrix_commute:
  "commutative f ⟹ commutative (combine_infmatrix f)"
by (simp add: commutative_def combine_infmatrix_def)

lemma combine_matrix_commute:
"commutative f ⟹ commutative (combine_matrix f)"
by (simp add: combine_matrix_def commutative_def combine_infmatrix_def)

text{*
On the contrary, given an associative function $f$ we cannot expect $f'$ to be associative. A counterexample is given by $A=\ganz$, $B=\{-1, 0, 1\}$,
as $f$ we take addition on $\ganz$, which is clearly associative. The abstraction is given by  $u(a) = 0$ for $a \notin B$. Then we have
\[ f' (f' 1 1) -1 = u(f (u (f 1 1)) -1) = u(f (u 2) -1) = u (f 0 -1) = -1, \]
but on the other hand we have
\[ f' 1 (f' 1 -1) = u (f 1 (u (f 1 -1))) = u (f 1 0) = 1.\]
A way out of this problem is to assume that $f(A\times A)\subset A$ holds, and this is what we are going to do:
*}

lemma nonzero_positions_combine_infmatrix[simp]: "f 0 0 = 0 ⟹ nonzero_positions (combine_infmatrix f A B) ⊆ (nonzero_positions A) ∪ (nonzero_positions B)"
apply(rule subsetI)
apply(simp add:nonzero_positions_def)
apply auto
done

lemma finite_nonzero_positions_Rep[simp]: "finite (nonzero_positions (Rep_matrix A))"
by (insert Rep_matrix [of A], simp add: matrix_def)

lemma combine_infmatrix_closed [simp]: "f 0 0 = 0 ⟹ Rep_matrix (Abs_matrix (combine_infmatrix f (Rep_matrix A) (Rep_matrix B))) = combine_infmatrix f (Rep_matrix A) (Rep_matrix B)"
apply (rule Abs_matrix_inverse)
apply (simp add: matrix_def)
proof -
have g:" f 0 0 = 0 ⟹ finite (nonzero_positions (combine_infmatrix f (Rep_matrix A) (Rep_matrix B)))"
apply (rule finite_subset[of _ "(nonzero_positions (Rep_matrix A)) ∪ (nonzero_positions (Rep_matrix B))"])
by (simp_all)
have d:" (fst ` nonzero_positions (combine_infmatrix f (Rep_matrix A) (Rep_matrix B))) =
          fst ` {(a,b).  (combine_infmatrix f (Rep_matrix A) (Rep_matrix B)) a b ≠ 0}"
by (metis (no_types, lifting) Collect_cong nonzero_positions_def split_beta')
have e:" fst ` {(a,b).  (combine_infmatrix f (Rep_matrix A) (Rep_matrix B)) a b ≠ 0}=
        {y. ∃a. (combine_infmatrix f (Rep_matrix A) (Rep_matrix B)) y a≠0 }"
        apply auto
        apply force
        done
have c:"{y. ∃a. (combine_infmatrix f (Rep_matrix A) (Rep_matrix B)) y a≠0 }=
       (fst ` nonzero_positions (combine_infmatrix f (Rep_matrix A) (Rep_matrix B)))"
using d e by auto
have a: "f 0 0=0⟹{y. ∃a. (combine_infmatrix f (Rep_matrix A) (Rep_matrix B)) y a≠0 }≠{}
        ∧ Max {y. ∃a. (combine_infmatrix f (Rep_matrix A) (Rep_matrix B)) y a≠0 } ≥ infinite⟹
     ∃yy≥infinite.  ∃a. (combine_infmatrix f (Rep_matrix A) (Rep_matrix B)) yy a≠0"
proof -
  assume a1: "{y. ∃a. combine_infmatrix f (Rep_matrix A) (Rep_matrix B) y a ≠ 0} ≠ {} ∧ infinite ≤ Max {y. ∃a. combine_infmatrix f (Rep_matrix A) (Rep_matrix B) y a ≠ 0}"
  assume a2: "f 0 0 = 0"
  have f3: "infinite ≤ Max {n. ∃na. combine_infmatrix f (Rep_matrix A) (Rep_matrix B) n na ≠ 0}"
   using a1 by linarith
  have "finite (fst ` nonzero_positions (combine_infmatrix f (Rep_matrix A) (Rep_matrix B)))"
    using a2 by (simp add: g)
  hence "Max {n. ∃na. combine_infmatrix f (Rep_matrix A) (Rep_matrix B) n na ≠ 0} ∈ {n. ∃na. combine_infmatrix f (Rep_matrix A) (Rep_matrix B) n na ≠ 0}"
   by (metis Max_in a1 c)  
  thus ?thesis
    using f3 by blast
qed
 have b: " f 0 0=0⟹(snd ` nonzero_positions (combine_infmatrix f (Rep_matrix A) (Rep_matrix B)))≠{}
      ∧Max (snd ` nonzero_positions (combine_infmatrix f (Rep_matrix A) (Rep_matrix B))) ≥ infinite⟹
     ∃yy. yy≥infinite∧ yy∈{y. ∃a. (combine_infmatrix f (Rep_matrix A) (Rep_matrix B)) a y ≠0}"
proof -
  assume a1: "f 0 0 = 0"
  assume a2: "snd ` nonzero_positions (combine_infmatrix f (Rep_matrix A) (Rep_matrix B)) ≠ {} ∧ infinite ≤ Max (snd ` nonzero_positions (combine_infmatrix f (Rep_matrix A) (Rep_matrix B)))"
  have f3: "∀f r. f ` r = {n. ∃p. (p∷nat × nat) ∈ r ∧ (n∷nat) = f p}"
    by blast
  hence "(snd ` nonzero_positions (combine_infmatrix f (Rep_matrix A) (Rep_matrix B)) ≠ {}) = ({n. ∃p. p ∈ {p. combine_infmatrix f (Rep_matrix A) (Rep_matrix B) (fst p) (snd p) ≠ 0} ∧ n = snd p} ≠ {})"
    using nonzero_positions_def by presburger
  hence f4: "{n. ∃p. p ∈ {p. combine_infmatrix f (Rep_matrix A) (Rep_matrix B) (fst p) (snd p) ≠ 0} ∧ n = snd p} ≠ {}"
    using a2 by blast
  have f5: "∀r f. ¬ finite r ∨ finite {n. ∃p. (p∷nat × nat) ∈ r ∧ (n∷nat) = f p}"
    using f3 by (metis (no_types) finite_imageI)
  have "finite {p. combine_infmatrix f (Rep_matrix A) (Rep_matrix B) (fst p) (snd p) ≠ 0}"
    using a1 g nonzero_positions_def by fastforce
  hence f6: "finite {n. ∃p. p ∈ {p. combine_infmatrix f (Rep_matrix A) (Rep_matrix B) (fst p) (snd p) ≠ 0} ∧ n = snd p}"
    using f5 by blast
  have "Max {n. ∃p. p ∈ {p. combine_infmatrix f (Rep_matrix A) (Rep_matrix B) (fst p) (snd p) ≠ 0} ∧ n = snd p} ∈ Collect (op ≤ infinite)"
    using f3 a2 by (simp add: nonzero_positions_def)
  thus ?thesis
    using f6 f4 Max_in by fastforce
qed
have c :"f 0 0=0⟹∀a≥infinite.∀b.(combine_infmatrix f (Rep_matrix A) (Rep_matrix B)) a b=0"
using dual_order.trans nrows by force
have d:"f 0 0=0⟹∀a≥infinite.∀b.(combine_infmatrix f (Rep_matrix A) (Rep_matrix B)) b a=0"
using dual_order.trans ncols by force
have e:" f 0 0 = 0 ⟹(fst ` nonzero_positions (combine_infmatrix f (Rep_matrix A) (Rep_matrix B)))≠{}⟹  Max (fst ` nonzero_positions (combine_infmatrix f (Rep_matrix A) (Rep_matrix B))) < infinite"
proof -
  assume a1: "fst ` nonzero_positions (combine_infmatrix f (Rep_matrix A) (Rep_matrix B)) ≠ {}"
  assume a2: "f 0 0 = 0"
  have f3: "∀f r. f ` r = {n. ∃p. (p∷nat × nat) ∈ r ∧ (n∷nat) = f p}"
    by (simp add: Bex_def_raw image_def)
  have f4: "{n. ∃p. p ∈ {p. combine_infmatrix f (Rep_matrix A) (Rep_matrix B) (fst p) (snd p) ≠ 0} ∧ n = fst p} ≠ {}"
    using a1 nonzero_positions_def by fastforce
  have f5: "finite {p. combine_infmatrix f (Rep_matrix A) (Rep_matrix B) (fst p) (snd p) ≠ 0}"
    using a2 g nonzero_positions_def by force
  have "∀r f. ¬ finite r ∨ finite {n. ∃p. (p∷nat × nat) ∈ r ∧ (n∷nat) = f p}"
    using f3 by (metis (no_types) finite_imageI)
  hence "finite {n. ∃p. p ∈ {p. combine_infmatrix f (Rep_matrix A) (Rep_matrix B) (fst p) (snd p) ≠ 0} ∧ n = fst p}"
    using f5 by presburger
  hence "infinite ∈ Collect (op < (Max {n. ∃p. p ∈ {p. combine_infmatrix f (Rep_matrix A) (Rep_matrix B) (fst p) (snd p) ≠ 0} ∧ n = fst p}))"
    using f4 a2 Max_in c by fastforce
  thus ?thesis
    using f3 by (simp add: nonzero_positions_def)
qed


have f:" f 0 0 = 0 ⟹
    (nonzero_positions (combine_infmatrix f (Rep_matrix A) (Rep_matrix B)) ≠ {} ⟶
     Max (fst ` nonzero_positions (combine_infmatrix f (Rep_matrix A) (Rep_matrix B))) < infinite ∧
     Max (snd ` nonzero_positions (combine_infmatrix f (Rep_matrix A) (Rep_matrix B))) < infinite)"
using b d e not_less by auto
show " f 0 0 = 0 ⟹
    finite (nonzero_positions (combine_infmatrix f (Rep_matrix A) (Rep_matrix B))) ∧
    (nonzero_positions (combine_infmatrix f (Rep_matrix A) (Rep_matrix B)) ≠ {} ⟶
     Max (fst ` nonzero_positions (combine_infmatrix f (Rep_matrix A) (Rep_matrix B))) < infinite ∧
     Max (snd ` nonzero_positions (combine_infmatrix f (Rep_matrix A) (Rep_matrix B))) < infinite)"
using `f 0 0 = 0 ⟹ finite (nonzero_positions (combine_infmatrix f (Rep_matrix A) (Rep_matrix B)))` f by blast
qed
text {* We need the next two lemmas only later, but it is analog to the above one, so we prove them now: *}
lemma nonzero_positions_apply_infmatrix[simp]: "f 0 = 0 ⟹ nonzero_positions (apply_infmatrix f A) ⊆ nonzero_positions A"
by (rule subsetI, simp add: nonzero_positions_def apply_infmatrix_def, auto)

lemma apply_infmatrix_closed [simp]: "f 0 = 0 ⟹ Rep_matrix (Abs_matrix (apply_infmatrix f (Rep_matrix A))) = apply_infmatrix f (Rep_matrix A)"
apply (rule Abs_matrix_inverse)
apply (simp add: matrix_def)
proof -
have a:"f 0 = 0 ⟹ finite (nonzero_positions (apply_infmatrix f (Rep_matrix A)))"
by (meson finite_nonzero_positions_Rep nonzero_positions_apply_infmatrix rev_finite_subset)
have bb: " f 0=0⟹(snd ` nonzero_positions (apply_infmatrix f (Rep_matrix A) ))≠{}
      ∧Max (snd ` nonzero_positions (apply_infmatrix f (Rep_matrix A) )) ≥ infinite⟹
     ∃yy. yy≥infinite∧ yy∈{y. ∃a. (apply_infmatrix f (Rep_matrix A)) a y ≠0}"
proof -
  assume a1: "f 0 = 0"
  assume a2: "snd ` nonzero_positions (apply_infmatrix f (Rep_matrix A)) ≠ {} ∧ infinite ≤ Max (snd ` nonzero_positions (apply_infmatrix f (Rep_matrix A)))"
  have f3: "∀f r. f ` r = {n. ∃p. (p∷nat × nat) ∈ r ∧ (n∷nat) = f p}"
    by blast
  hence "(snd ` nonzero_positions (apply_infmatrix f (Rep_matrix A)) ≠ {}) = ({n. ∃p. p ∈ {p. apply_infmatrix f (Rep_matrix A) (fst p) (snd p) ≠ 0} ∧ n = snd p} ≠ {})"
    using nonzero_positions_def by presburger
  hence f4: "{n. ∃p. p ∈ {p. apply_infmatrix f (Rep_matrix A) (fst p) (snd p) ≠ 0} ∧ n = snd p} ≠ {}"
using a2 by blast
  have f5: "∀r f. ¬ finite r ∨ finite {n. ∃p. (p∷nat × nat) ∈ r ∧ (n∷nat) = f p}"
    using f3 by (metis (no_types) finite_imageI)
  have "finite {p. apply_infmatrix f (Rep_matrix A) (fst p) (snd p) ≠ 0}"
    using a1 a nonzero_positions_def by fastforce
  hence "finite {n. ∃p. p ∈ {p. apply_infmatrix f (Rep_matrix A) (fst p) (snd p) ≠ 0} ∧ n = snd p}"
    using f5 by blast
  hence "∃n. apply_infmatrix f (Rep_matrix A) n (Max {n. ∃p. p ∈ {p. apply_infmatrix f (Rep_matrix A) (fst p) (snd p) ≠ 0} ∧ n = snd p}) ≠ 0"
    using f4 Max_in by fastforce
  thus ?thesis
    using f3 a2 nonzero_positions_def by force
qed
have b: " f 0=0⟹(fst ` nonzero_positions (apply_infmatrix f (Rep_matrix A) ))≠{}
      ∧Max (fst ` nonzero_positions (apply_infmatrix f (Rep_matrix A) )) ≥ infinite⟹
     ∃yy. yy≥infinite∧ yy∈{y. ∃a. (apply_infmatrix f (Rep_matrix A)) y a ≠0}"
proof -
  assume a1: "f 0 = 0"
  assume a2: "fst ` nonzero_positions (apply_infmatrix f (Rep_matrix A)) ≠ {} ∧ infinite ≤ Max (fst ` nonzero_positions (apply_infmatrix f (Rep_matrix A)))"
  have f3: "∀f r. f ` r = {n. ∃p. (p∷nat × nat) ∈ r ∧ (n∷nat) = f p}"
    by blast
  hence "(fst ` nonzero_positions (apply_infmatrix f (Rep_matrix A)) ≠ {}) = ({n. ∃p. p ∈ {p. apply_infmatrix f (Rep_matrix A) (fst p) (snd p) ≠ 0} ∧ n = fst p} ≠ {})"
    using nonzero_positions_def by presburger
  hence f4: "{n. ∃p. p ∈ {p. apply_infmatrix f (Rep_matrix A) (fst p) (snd p) ≠ 0} ∧ n = fst p} ≠ {}"
using a2 by blast
  have f5: "∀r f. ¬ finite r ∨ finite {n. ∃p. (p∷nat × nat) ∈ r ∧ (n∷nat) = f p}"
    using f3 by (metis (no_types) finite_imageI)
  have "finite {p. apply_infmatrix f (Rep_matrix A) (fst p) (snd p) ≠ 0}"
    using a1 a nonzero_positions_def by fastforce
  hence "finite {n. ∃p. p ∈ {p. apply_infmatrix f (Rep_matrix A) (fst p) (snd p) ≠ 0} ∧ n = fst p}"
    using f5 by blast
  hence "∃n. apply_infmatrix f (Rep_matrix A) (Max {n. ∃p. p ∈ {p. apply_infmatrix f (Rep_matrix A) (fst p) (snd p) ≠ 0} ∧ n = fst p}) n ≠ 0"
    using f4 Max_in by fastforce
  thus ?thesis
    using f3 a2 nonzero_positions_def by auto
qed
have cc:"f 0=0⟹∀a.∀b≥infinite. (apply_infmatrix f (Rep_matrix A)) b a=0"
by (metis expand_apply_infmatrix ncols_max ncols_transpose nrows_le)
have c:"f 0 = 0 ⟹nonzero_positions (apply_infmatrix f (Rep_matrix A)) ≠ {} ⟹ Max (fst ` nonzero_positions (apply_infmatrix f (Rep_matrix A))) < infinite"
using b cc by auto
have c:"f 0=0⟹∀a.∀b≥infinite. (apply_infmatrix f (Rep_matrix A)) a b=0"
by (metis expand_apply_infmatrix le_trans ncols ncols_max)
have d:"f 0 = 0 ⟹nonzero_positions (apply_infmatrix f (Rep_matrix A)) ≠ {} ⟹ Max (snd ` nonzero_positions (apply_infmatrix f (Rep_matrix A))) < infinite"
using bb c by auto
show " f 0 = 0 ⟹
    finite (nonzero_positions (apply_infmatrix f (Rep_matrix A))) ∧
    (nonzero_positions (apply_infmatrix f (Rep_matrix A)) ≠ {} ⟶
     Max (fst ` nonzero_positions (apply_infmatrix f (Rep_matrix A))) < infinite ∧
     Max (snd ` nonzero_positions (apply_infmatrix f (Rep_matrix A))) < infinite) "
using a b cc d by fastforce
qed

lemma combine_infmatrix_assoc[simp]: "f 0 0 = 0 ⟹ associative f ⟹ associative (combine_infmatrix f)"
by (simp add: associative_def combine_infmatrix_def)

lemma comb: "f = g ⟹ x = y ⟹ f x = g y"
by (auto)

lemma combine_matrix_assoc: "f 0 0 = 0 ⟹ associative f ⟹ associative (combine_matrix f)"
apply (simp(no_asm) add: associative_def combine_matrix_def, auto)
apply (rule comb [of Abs_matrix Abs_matrix])
by (auto, insert combine_infmatrix_assoc[of f], simp add: associative_def)

lemma Rep_apply_matrix[simp]: "f 0 = 0 ⟹ Rep_matrix (apply_matrix f A) j i = f (Rep_matrix A j i)"
by (simp add: apply_matrix_def)

lemma Rep_combine_matrix[simp]: "f 0 0 = 0 ⟹ Rep_matrix (combine_matrix f A B) j i = f (Rep_matrix A j i) (Rep_matrix B j i)"
  by(simp add: combine_matrix_def)

lemma combine_nrows_max: "f 0 0 = 0  ⟹ nrows (combine_matrix f A B) <= max (nrows A) (nrows B)"
by (simp add: nrows_le)

lemma combine_ncols_max: "f 0 0 = 0 ⟹ ncols (combine_matrix f A B) <= max (ncols A) (ncols B)"
by (simp add: ncols_le)

lemma combine_nrows: "f 0 0 = 0 ⟹ nrows A <= q ⟹ nrows B <= q ⟹ nrows(combine_matrix f A B) <= q"
  by (simp add: nrows_le)

lemma combine_ncols: "f 0 0 = 0 ⟹ ncols A <= q ⟹ ncols B <= q ⟹ ncols(combine_matrix f A B) <= q"
  by (simp add: ncols_le)

definition zero_r_neutral :: "('a ⇒ 'b::zero ⇒ 'a) ⇒ bool" where
  "zero_r_neutral f == ! a. f a 0 = a"

definition zero_l_neutral :: "('a::zero ⇒ 'b ⇒ 'b) ⇒ bool" where
  "zero_l_neutral f == ! a. f 0 a = a"

definition zero_closed :: "(('a::zero) ⇒ ('b::zero) ⇒ ('c::zero)) ⇒ bool" where
  "zero_closed f == (!x. f x 0 = 0) & (!y. f 0 y = 0)"

(*   calculate A*B    *)
primrec foldseq :: "('a ⇒ 'a ⇒ 'a) ⇒ (nat ⇒ 'a) ⇒ nat ⇒ 'a"
where
  "foldseq f s 0 = s 0"
| "foldseq f s (Suc n) = f (s 0) (foldseq f (% k. s(Suc k)) n)"

primrec foldseq_transposed ::  "('a ⇒ 'a ⇒ 'a) ⇒ (nat ⇒ 'a) ⇒ nat ⇒ 'a"
where
  "foldseq_transposed f s 0 = s 0"
| "foldseq_transposed f s (Suc n) = f (foldseq_transposed f s n) (s (Suc n))"

lemma foldseq_assoc : "associative f ⟹ foldseq f = foldseq_transposed f"
proof -
  assume a:"associative f"
  then have sublemma: "!! n. ! N s. N <= n ⟶ foldseq f s N = foldseq_transposed f s N"
  proof -
    fix n
    show "!N s. N <= n ⟶ foldseq f s N = foldseq_transposed f s N"
    proof (induct n)
      show "!N s. N <= 0 ⟶ foldseq f s N = foldseq_transposed f s N" by simp
    next
      fix n
      assume b:"! N s. N <= n ⟶ foldseq f s N = foldseq_transposed f s N"
      have c:"!!N s. N <= n ⟹ foldseq f s N = foldseq_transposed f s N" by (simp add: b)
      show "! N t. N <= Suc n ⟶ foldseq f t N = foldseq_transposed f t N"
      proof (auto)
        fix N t
        assume Nsuc: "N <= Suc n"
        show "foldseq f t N = foldseq_transposed f t N"
        proof cases
          assume "N <= n"
          then show "foldseq f t N = foldseq_transposed f t N" by (simp add: b)
        next
          assume "~(N <= n)"
          with Nsuc have Nsuceq: "N = Suc n" by simp
          have neqz: "n ≠ 0 ⟹ ? m. n = Suc m & Suc m <= n" by arith
          have assocf: "!! x y z. f x (f y z) = f (f x y) z" by (insert a, simp add: associative_def)
          show "foldseq f t N = foldseq_transposed f t N"
            apply (simp add: Nsuceq)
            apply (subst c)
            apply (simp)
            apply (case_tac "n = 0")
            apply (simp)
            apply (drule neqz)
            apply (erule exE)
            apply (simp)
            apply (subst assocf)
            proof -
              fix m
              assume "n = Suc m & Suc m <= n"
              then have mless: "Suc m <= n" by arith
              then have step1: "foldseq_transposed f (% k. t (Suc k)) m = foldseq f (% k. t (Suc k)) m" (is "?T1 = ?T2")
                apply (subst c)
                by simp+
              have step2: "f (t 0) ?T2 = foldseq f t (Suc m)" (is "_ = ?T3") by simp
              have step3: "?T3 = foldseq_transposed f t (Suc m)" (is "_ = ?T4")
                apply (subst c)
                by (simp add: mless)+
              have step4: "?T4 = f (foldseq_transposed f t m) (t (Suc m))" (is "_=?T5") by simp
              from step1 step2 step3 step4 show sowhat: "f (f (t 0) ?T1) (t (Suc (Suc m))) = f ?T5 (t (Suc (Suc m)))" by simp
            qed
          qed
        qed
      qed
    qed
    show "foldseq f = foldseq_transposed f" by ((rule ext)+, insert sublemma, auto)
  qed

lemma foldseq_distr: "⟦associative f; commutative f⟧ ⟹ foldseq f (% k. f (u k) (v k)) n = f (foldseq f u n) (foldseq f v n)"
proof -
  assume assoc: "associative f"
  assume comm: "commutative f"
  from assoc have a:"!! x y z. f (f x y) z = f x (f y z)" by (simp add: associative_def)
  from comm have b: "!! x y. f x y = f y x" by (simp add: commutative_def)
  from assoc comm have c: "!! x y z. f x (f y z) = f y (f x z)" by (simp add: commutative_def associative_def)
  have "!! n. (! u v. foldseq f (%k. f (u k) (v k)) n = f (foldseq f u n) (foldseq f v n))"
    apply (induct_tac n)
    apply (simp+, auto)
    by (simp add: a b c)
  then show "foldseq f (% k. f (u k) (v k)) n = f (foldseq f u n) (foldseq f v n)" by simp
qed

theorem "⟦associative f; associative g; ∀a b c d. g (f a b) (f c d) = f (g a c) (g b d); ? x y. (f x) ≠ (f y); ? x y. (g x) ≠ (g y); f x x = x; g x x = x⟧ ⟹ f=g | (! y. f y x = y) | (! y. g y x = y)"
oops
(* Model found

Trying to find a model that refutes: ⟦associative f; associative g;
 ∀a b c d. g (f a b) (f c d) = f (g a c) (g b d); ∃x y. f x ≠ f y;
 ∃x y. g x ≠ g y; f x x = x; g x x = x⟧
⟹ f = g ∨ (∀y. f y x = y) ∨ (∀y. g y x = y)
Searching for a model of size 1, translating term... invoking SAT solver... no model found.
Searching for a model of size 2, translating term... invoking SAT solver... no model found.
Searching for a model of size 3, translating term... invoking SAT solver...
Model found:
Size of types: 'a: 3
x: a1
g: (a0↦(a0↦a1, a1↦a0, a2↦a1), a1↦(a0↦a0, a1↦a1, a2↦a0), a2↦(a0↦a1, a1↦a0, a2↦a1))
f: (a0↦(a0↦a0, a1↦a0, a2↦a0), a1↦(a0↦a1, a1↦a1, a2↦a1), a2↦(a0↦a0, a1↦a0, a2↦a0))
*)


lemma foldseq_zero:
assumes fz: "f 0 0 = 0" and sz: "! i. i <= n ⟶ s i = 0"
shows "foldseq f s n = 0"
proof -
  have "!! n. ! s. (! i. i <= n ⟶ s i = 0) ⟶ foldseq f s n = 0"
    apply (induct_tac n)
    apply (simp)
    by (simp add: fz)
  then show "foldseq f s n = 0"
 by (simp add: sz)
qed

lemma foldseq1_significant_positions:
  assumes p: "! i. i <= N ⟶ S i = T i"
  shows "foldseq_transposed f S N = foldseq_transposed f T N"
proof -
  have "!! m . ! s t. (! i. i<=m ⟶ s i = t i) ⟶ foldseq_transposed f s m =  foldseq_transposed f t m"
    apply (induct_tac m)
    apply (simp)
    apply (simp)
    apply (auto)
    proof -
      fix n
      fix s::"nat⇒'a"
      fix t::"nat⇒'a"
      assume a: "∀s t. (∀i≤n. s i = t i) ⟶ foldseq_transposed f s n = foldseq_transposed f t n"
      assume b: "∀i≤Suc n. s i = t i"
      have c:"!! a b. a = b ⟹ f (t 0) a = f (t 0) b" by blast
      have d:"!! s t. (∀i≤n. s i = t i) ⟹foldseq_transposed f s n = foldseq_transposed f t n"  by (simp add: a)
      show " f (foldseq_transposed f s n) (t (Suc n)) = f (foldseq_transposed f t n) (t (Suc n))" by (metis a b le_SucI)
    qed
  with p show ?thesis by simp
qed

lemma foldseq_significant_positions:
  assumes p: "! i. i <= N ⟶ S i = T i"
  shows "foldseq f S N = foldseq f T N"
proof -
  have "!! m . ! s t. (! i. i<=m ⟶ s i = t i) ⟶ foldseq f s m = foldseq f t m"
    apply (induct_tac m)
    apply (simp)
    apply (simp)
    apply (auto)
    proof -
      fix n
      fix s::"nat⇒'a"
      fix t::"nat⇒'a"
      assume a: "∀s t. (∀i≤n. s i = t i) ⟶ foldseq f s n = foldseq f t n"
      assume b: "∀i≤Suc n. s i = t i"
      have c:"!! a b. a = b ⟹ f (t 0) a = f (t 0) b" by blast
      have d:"!! s t. (∀i≤n. s i = t i) ⟹ foldseq f s n = foldseq f t n" by (simp add: a)
      show "f (t 0) (foldseq f (λk. s (Suc k)) n) = f (t 0) (foldseq f (λk. t (Suc k)) n)" by (rule c, simp add: d b)
    qed
  with p show ?thesis by simp
qed

lemma foldseq_tail:
  assumes "M <= N"
  shows "foldseq f S N = foldseq f (% k. (if k < M then (S k) else (foldseq f (% k. S(k+M)) (N-M)))) M"
proof -
  have suc: "!! a b. ⟦a <= Suc b; a ≠ Suc b⟧ ⟹ a <= b" by arith
  have a:"!! a b c . a = b ⟹ f c a = f c b" by blast
  have "!! n. ! m s. m <= n ⟶ foldseq f s n = foldseq f (% k. (if k < m then (s k) else (foldseq f (% k. s(k+m)) (n-m)))) m"
    apply (induct_tac n)
    apply (simp)
    apply (simp)
    apply (auto)
    apply (case_tac "m = Suc na")
    apply (simp)
    apply (rule a)
    apply (rule foldseq_significant_positions)
    apply (auto)
    apply (drule suc, simp+)
    proof -
      fix na m s
      assume suba:"∀m≤na. ∀s. foldseq f s na = foldseq f (λk. if k < m then s k else foldseq f (λk. s (k + m)) (na - m))m"
      assume subb:"m <= na"
      from suba have subc:"!! m s. m <= na ⟹foldseq f s na = foldseq f (λk. if k < m then s k else foldseq f (λk. s (k + m)) (na - m))m" by simp
      have subd: "foldseq f (λk. if k < m then s (Suc k) else foldseq f (λk. s (Suc (k + m))) (na - m)) m =
        foldseq f (% k. s(Suc k)) na"
        by (rule subc[of m "% k. s(Suc k)", THEN sym], simp add: subb)
      from subb have sube: "m ≠ 0 ⟹ ? mm. m = Suc mm & mm <= na" by arith
      show "f (s 0) (foldseq f (λk. if k < m then s (Suc k) else foldseq f (λk. s (Suc (k + m))) (na - m)) m) =
        foldseq f (λk. if k < m then s k else foldseq f (λk. s (k + m)) (Suc na - m)) m"
        apply (simp add: subd)
        apply (cases "m = 0")
        apply (simp)
        apply (drule sube)
        apply (auto)
        apply (rule a)
        by (simp add: subc cong del: if_cong)
    qed
  then show ?thesis using assms by simp
qed


lemma foldseq_zerotail:
  assumes
  fz: "f 0 0 = 0"
  and sz: "! i.  n <= i ⟶ s i = 0"
  and nm: "n <= m"
  shows
  "foldseq f s n = foldseq f s m"
proof -
  show "foldseq f s n = foldseq f s m"
    apply (simp add: foldseq_tail[OF nm, of f s])
    apply (rule foldseq_significant_positions)
    apply (auto)
    apply (subst foldseq_zero)
    by (simp add: fz sz)+
qed

lemma foldseq_zerotail2:
  assumes "! x. f x 0 = x"
  and "! i. n < i ⟶ s i = 0"
  and nm: "n <= m"
  shows "foldseq f s n = foldseq f s m"
proof -
  have "f 0 0 = 0" by (simp add: assms)
  have b:"!! m n. n <= m ⟹ m ≠ n ⟹ ? k. m-n = Suc k" by arith
  have c: "0 <= m" by simp
  have d: "!! k. k ≠ 0 ⟹ ? l. k = Suc l" by arith
  show ?thesis
    apply (subst foldseq_tail[OF nm])
    apply (rule foldseq_significant_positions)
    apply (auto)
    apply (case_tac "m=n")
    apply (simp+)
    apply (drule b[OF nm])
    apply (auto)
    apply (case_tac "k=0")
    apply (simp add: assms)
    apply (drule d)
    apply (auto)
    apply (simp add: assms foldseq_zero)
    done
qed

lemma foldseq_zerostart:
  "! x. f 0 (f 0 x) = f 0 x ⟹  ! i. i <= n ⟶ s i = 0 ⟹ foldseq f s (Suc n) = f 0 (s (Suc n))"
proof -
  assume f00x: "! x. f 0 (f 0 x) = f 0 x"
  have "! s. (! i. i<=n ⟶ s i = 0) ⟶ foldseq f s (Suc n) = f 0 (s (Suc n))"
    apply (induct n)
    apply (simp)
    apply (rule allI, rule impI)
    proof -
      fix n
      fix s
      have a:"foldseq f s (Suc (Suc n)) = f (s 0) (foldseq f (% k. s(Suc k)) (Suc n))" by simp
      assume b: "! s. ((∀i≤n. s i = 0) ⟶ foldseq f s (Suc n) = f 0 (s (Suc n)))"
      from b have c:"!! s. (∀i≤n. s i = 0) ⟹ foldseq f s (Suc n) = f 0 (s (Suc n))" by simp
      assume d: "! i. i <= Suc n ⟶ s i = 0"
      show "foldseq f s (Suc (Suc n)) = f 0 (s (Suc (Suc n)))"
        apply (subst a)
        apply (subst c)
        by (simp add: d f00x)+
    qed
  then show "! i. i <= n ⟶ s i = 0 ⟹ foldseq f s (Suc n) = f 0 (s (Suc n))" by simp
qed

lemma foldseq_zerostart2:
  "! x. f 0 x = x ⟹  ! i. i < n ⟶ s i = 0 ⟹ foldseq f s n = s n"
proof -
  assume a:"! i. i<n ⟶ s i = 0"
  assume x:"! x. f 0 x = x"
  from x have f00x: "! x. f 0 (f 0 x) = f 0 x" by blast
  have b: "!! i l. i < Suc l = (i <= l)" by arith
  have d: "!! k. k ≠ 0 ⟹ ? l. k = Suc l" by arith
  show "foldseq f s n = s n"
  apply (case_tac "n=0")
  apply (simp)
  apply (insert a)
  apply (drule d)
  apply (auto)
  apply (simp add: b)
  apply (insert f00x)
  apply (drule foldseq_zerostart)
  by (simp add: x)+
qed

lemma foldseq_almostzero:
  assumes f0x:"! x. f 0 x = x" and fx0: "! x. f x 0 = x" and s0:"! i. i ≠ j ⟶ s i = 0"
  shows "foldseq f s n = (if (j <= n) then (s j) else 0)"
proof -
  from s0 have a: "! i. i < j ⟶ s i = 0" by simp
  from s0 have b: "! i. j < i ⟶ s i = 0" by simp
  show ?thesis
    apply auto
    apply (subst foldseq_zerotail2[of f, OF fx0, of j, OF b, of n, THEN sym])
    apply simp
    apply (subst foldseq_zerostart2)
    apply (simp add: f0x a)+
    apply (subst foldseq_zero)
    by (simp add: s0 f0x)+
qed

lemma foldseq_distr_unary:
  assumes "!! a b. g (f a b) = f (g a) (g b)"
  shows "g(foldseq f s n) = foldseq f (% x. g(s x)) n"
proof -
  have "! s. g(foldseq f s n) = foldseq f (% x. g(s x)) n"
    apply (induct_tac n)
    apply (simp)
    apply (simp)
    apply (auto)
    apply (drule_tac x="% k. s (Suc k)" in spec)
    by (simp add: assms)
  then show ?thesis by simp
qed

definition mult_matrix_n :: "nat ⇒ (real⇒real⇒real) ⇒ (real⇒real⇒real) ⇒matrix ⇒matrix ⇒matrix" where
  "mult_matrix_n n fmul fadd A B == Abs_matrix(% j i. foldseq fadd (% k. fmul (Rep_matrix A j k) (Rep_matrix B k i)) n)"
  definition mult_matrix_n1 :: "nat ⇒ (real⇒real⇒real) ⇒ (real⇒real⇒real) ⇒matrix ⇒matrix ⇒matrix" where
  "mult_matrix_n1 n fmul fadd A B == Abs_matrix(% j i. foldseq_transposed fadd (% k. fmul (Rep_matrix A j k) (Rep_matrix B k i)) n)"
definition mult_matrix1 :: "(real⇒real⇒real) ⇒  (real⇒real⇒real) ⇒ matrix ⇒matrix ⇒matrix" where
  "mult_matrix1 fmul fadd A B == mult_matrix_n1 (max (ncols A) (nrows B)) fmul fadd A B"
definition mult_matrix :: "(real⇒real⇒real) ⇒  (real⇒real⇒real) ⇒ matrix ⇒matrix ⇒matrix" where
  "mult_matrix fmul fadd A B == mult_matrix_n (max (ncols A) (nrows B)) fmul fadd A B"


definition tr_n:: "nat ⇒ (real⇒real⇒real) ⇒ matrix⇒real" where
   "tr_n n fadd A==foldseq fadd (%k. Rep_matrix A k k) n"
definition tr::"(real⇒real⇒real) ⇒ matrix⇒real"where
   "tr fadd A==foldseq fadd (%k. Rep_matrix A k k) (max (nrows A) (ncols A)) "


lemma mult_matrix_n:
  assumes "ncols A ≤  n" (is ?An) "nrows B ≤ n" (is ?Bn) "fadd 0 0 = 0" "fmul 0 0 = 0"
  shows c:"mult_matrix fmul fadd A B = mult_matrix_n n fmul fadd A B"
proof -
  show ?thesis using assms
    apply (simp add: mult_matrix_def mult_matrix_n_def)
    apply (rule comb[of "Abs_matrix" "Abs_matrix"], simp, (rule ext)+)
    apply (rule foldseq_zerotail, simp_all add: nrows_le ncols_le assms)
    done
qed


lemma mult_matrix_nm:
  assumes "ncols A <= n" "nrows B <= n" "ncols A <= m" "nrows B <= m" "fadd 0 0 = 0" "fmul 0 0 = 0"
  shows "mult_matrix_n n fmul fadd A B = mult_matrix_n m fmul fadd A B"
proof -
  from assms have "mult_matrix_n n fmul fadd A B = mult_matrix fmul fadd A B"
    by (simp add: mult_matrix_n)
  also from assms have "… = mult_matrix_n m fmul fadd A B"
    by (simp add: mult_matrix_n[THEN sym])
  finally show "mult_matrix_n n fmul fadd A B = mult_matrix_n m fmul fadd A B" by simp
qed

definition r_distributive :: "('a ⇒ 'b ⇒ 'b) ⇒ ('b ⇒ 'b ⇒ 'b) ⇒ bool" where
  "r_distributive fmul fadd == ! a u v. fmul a (fadd u v) = fadd (fmul a u) (fmul a v)"

definition l_distributive :: "('a ⇒ 'b ⇒ 'a) ⇒ ('a ⇒ 'a ⇒ 'a) ⇒ bool" where
  "l_distributive fmul fadd == ! a u v. fmul (fadd u v) a = fadd (fmul u a) (fmul v a)"

definition distributive :: "('a ⇒ 'a ⇒ 'a) ⇒ ('a ⇒ 'a ⇒ 'a) ⇒ bool" where
  "distributive fmul fadd == l_distributive fmul fadd & r_distributive fmul fadd"

lemma max1: "!! a x y. (a::nat) <= x ⟹ a <= max x y" by (arith)
lemma max2: "!! b x y. (b::nat) <= y ⟹ b <= max x y" by (arith)

lemma r_distributive_matrix:
 assumes
  "r_distributive fmul fadd"
  "associative fadd"
  "commutative fadd"
  "fadd 0 0 = 0"
  "! a. fmul a 0 = 0"
  "! a. fmul 0 a = 0"
 shows "r_distributive (mult_matrix fmul fadd) (combine_matrix fadd)"
proof -
  from assms show ?thesis
    apply (simp add: r_distributive_def mult_matrix_def, auto)
    proof -
      fix a::"matrix"
      fix u::" matrix"
      fix v::" matrix"
      let ?mx = "max (ncols a) (max (nrows u) (nrows v))"
      from assms show "mult_matrix_n (max (ncols a) (nrows (combine_matrix fadd u v))) fmul fadd a (combine_matrix fadd u v) =
        combine_matrix fadd (mult_matrix_n (max (ncols a) (nrows u)) fmul fadd a u) (mult_matrix_n (max (ncols a) (nrows v)) fmul fadd a v)"     
        apply (subst mult_matrix_nm[of a _  _ ?mx fadd fmul])
        apply (simp add: max1 max2 combine_nrows combine_ncols)+
        apply (subst mult_matrix_nm[of a _ v ?mx fadd fmul])
        apply (simp add: max1 max2 combine_nrows combine_ncols)+
        apply (subst mult_matrix_nm[of a _ u ?mx fadd fmul])
        apply (simp add: max1 max2 combine_nrows combine_ncols)+
        apply (simp add: mult_matrix_n_def r_distributive_def foldseq_distr[of fadd])
        apply (simp add: combine_matrix_def combine_infmatrix_def)
        apply (rule comb[of "Abs_matrix" "Abs_matrix"], simp, (rule ext)+)
        apply (simplesubst RepAbs_matrix)
        apply (simp, auto)
        apply (rule exI[of _ "nrows a"], simp add: nrows_le foldseq_zero)
        apply (meson dual_order.trans nrows nrows_max)
        apply (rule exI[of _ "ncols v"], simp add: ncols_le foldseq_zero)
        apply (meson dual_order.trans ncols ncols_max)
        apply (subst RepAbs_matrix)
        apply (simp, auto)
        apply (rule exI[of _ "nrows a"], simp add: nrows_le foldseq_zero)
        apply (meson dual_order.trans nrows nrows_max)
        apply (rule exI[of _ "ncols u"], simp add: ncols_le foldseq_zero)
        apply (meson dual_order.trans ncols ncols_max)
        done
    qed
qed


lemma l_distributive_matrix:
 assumes
  "l_distributive fmul fadd"
  "associative fadd"
  "commutative fadd"
  "fadd 0 0 = 0"
  "! a. fmul a 0 = 0"
  "! a. fmul 0 a = 0"
 shows "l_distributive (mult_matrix fmul fadd) (combine_matrix fadd)"
proof -
  from assms show ?thesis
    apply (simp add: l_distributive_def mult_matrix_def, auto)
    proof -
      fix a::"matrix"
      fix u::" matrix"
      fix v::" matrix"
      let ?mx = "max (nrows a) (max (ncols u) (ncols v))"
      from assms show "mult_matrix_n (max (ncols (combine_matrix fadd u v)) (nrows a)) fmul fadd (combine_matrix fadd u v) a =
               combine_matrix fadd (mult_matrix_n (max (ncols u) (nrows a)) fmul fadd u a) (mult_matrix_n (max (ncols v) (nrows a)) fmul fadd v a)"
        apply (subst mult_matrix_nm[of v _ _ ?mx fadd fmul])
        apply (simp add: max1 max2 combine_nrows combine_ncols)+
        apply (subst mult_matrix_nm[of u _ _ ?mx fadd fmul])
        apply (simp add: max1 max2 combine_nrows combine_ncols)+
        apply (subst mult_matrix_nm[of _ _ _ ?mx fadd fmul])
        apply (simp add: max1 max2 combine_nrows combine_ncols)+
        apply (simp add: mult_matrix_n_def l_distributive_def foldseq_distr[of fadd])
        apply (simp add: combine_matrix_def combine_infmatrix_def)
        apply (rule comb[of "Abs_matrix" "Abs_matrix"], simp, (rule ext)+)
        apply (simplesubst RepAbs_matrix)
        apply (simp, auto)
        apply (rule exI[of _ "nrows v"], simp add: nrows_le foldseq_zero)
        apply (meson dual_order.trans nrows nrows_max)
        apply (rule exI[of _ "ncols a"], simp add: ncols_le foldseq_zero)
        apply (meson dual_order.trans ncols ncols_max)
        apply (subst RepAbs_matrix)
        apply (simp, auto)
        apply (rule exI[of _ "nrows u"], simp add: nrows_le foldseq_zero)
        apply (meson dual_order.trans nrows nrows_max)
        apply (rule exI[of _ "ncols a"], simp add: ncols_le foldseq_zero)
        apply (meson dual_order.trans ncols ncols_max)
        done
    qed
qed


definition zero_matrix_def: "zero = Abs_matrix (λj i. 0)"



lemma Rep_zero_matrix_def[simp]: "Rep_matrix zero j i = 0"
  apply (simp add: zero_matrix_def)
  apply (subst RepAbs_matrix)
  by (auto)

lemma zero_matrix_def_nrows[simp]: "nrows zero = 0"
proof -
  have a:"!! (x::nat). x <= 0 ⟹ x = 0" by (arith)
  show "nrows zero = 0" by (rule a, subst nrows_le, simp)
qed

lemma zero_matrix_def_ncols[simp]: "ncols zero = 0"
proof -
  have a:"!! (x::nat). x <= 0 ⟹ x = 0" by (arith)
  show "ncols zero = 0" by (rule a, subst ncols_le, simp)
qed


lemma mult_matrix_n_zero_right[simp]: "⟦fadd 0 0 = 0; !a. fmul a 0 = 0⟧ ⟹ mult_matrix_n n fmul fadd A zero = zero"
  apply (simp add: mult_matrix_n_def)
  apply (subst foldseq_zero)
  by (simp_all add: zero_matrix_def)

lemma mult_matrix_n_zero_left[simp]: "⟦fadd 0 0 = 0; !a. fmul 0 a = 0⟧ ⟹ mult_matrix_n n fmul fadd zero A = zero"
  apply (simp add: mult_matrix_n_def)
  apply (subst foldseq_zero)
  by (simp_all add: zero_matrix_def)

lemma mult_matrix_zero_left[simp]: "⟦fadd 0 0 = 0; !a. fmul 0 a = 0⟧ ⟹ mult_matrix fmul fadd zero A = zero"
by (simp add: mult_matrix_def)

lemma mult_matrix_zero_right[simp]: "⟦fadd 0 0 = 0; !a. fmul a 0 = 0⟧ ⟹ mult_matrix fmul fadd A zero = zero"
by (simp add: mult_matrix_def)

lemma apply_matrix_zero[simp]: "f 0 = 0 ⟹ apply_matrix f zero = zero"
  apply (simp add: apply_matrix_def apply_infmatrix_def)
  by (simp add: zero_matrix_def)

lemma combine_matrix_zero: "f 0 0 = 0 ⟹ combine_matrix f zero zero = zero"
  apply (simp add: combine_matrix_def combine_infmatrix_def)
  by (simp add: zero_matrix_def)

lemma transpose_matrix_zero[simp]: "transpose_matrix zero = zero"
apply (simp add: transpose_matrix_def zero_matrix_def RepAbs_matrix)
apply (subst Rep_matrix_inject[symmetric], (rule ext)+)
apply (simp add: RepAbs_matrix)
using zero_matrix_def by auto


lemma apply_zero_matrix_def[simp]: "apply_matrix (% x. 0) A = zero"
  apply (simp add: apply_matrix_def apply_infmatrix_def)
  by (simp add: zero_matrix_def)

definition singleton_matrix :: "nat ⇒ nat ⇒ real ⇒matrix" where
  "singleton_matrix j i a == Abs_matrix(% m n. if j = m & i = n then a else 0)"

definition move_matrix :: " matrix ⇒ int ⇒ int ⇒  matrix" where
  "move_matrix A y x == Abs_matrix(% j i. if (((int j)-y) < 0) | (((int i)-x) < 0) then 0 else Rep_matrix A (nat ((int j)-y)) (nat ((int i)-x)))"

definition take_rows :: " matrix ⇒ nat ⇒  matrix" where
  "take_rows A r == Abs_matrix(% j i. if (j < r) then (Rep_matrix A j i) else 0)"

definition take_columns :: " matrix ⇒ nat ⇒  matrix" where
  "take_columns A c == Abs_matrix(% j i. if (i < c) then (Rep_matrix A j i) else 0)"

definition column_of_matrix :: " matrix ⇒ nat ⇒  matrix" where
  "column_of_matrix A n == take_columns (move_matrix A 0 (- int n)) 1"

definition row_of_matrix :: " matrix ⇒ nat ⇒ matrix" where
  "row_of_matrix A m == take_rows (move_matrix A (- int m) 0) 1"

lemma Rep_singleton_matrix[simp]: "j<infinite∧i<infinite⟹Rep_matrix (singleton_matrix j i e) m n = (if j = m & i = n then e else 0)"
apply (simp add: singleton_matrix_def)
apply (auto)
apply (subst RepAbs_matrix)
apply (rule exI[of _ "Suc m"], simp)
apply (rule exI[of _ "Suc n"], simp+)
by (subst RepAbs_matrix, rule exI[of _ "Suc j"], simp, rule exI[of _ "Suc i"], simp+)+

lemma apply_singleton_matrix[simp]: "j<infinite∧i<infinite⟹f 0 = 0 ⟹ apply_matrix f (singleton_matrix j i x) = (singleton_matrix j i (f x))"
apply (subst Rep_matrix_inject[symmetric])
apply (rule ext)+
apply (simp)
done

lemma singleton_matrix_zero[simp]: "singleton_matrix j i 0 = zero"
  by (simp add: singleton_matrix_def zero_matrix_def)

lemma nrows_singleton[simp]: "(j<infinite∧i<infinite) ⟹ j<infinite∧(nrows(singleton_matrix j i e) = (if e = 0 then 0 else Suc j))"
proof-
have th: "¬ (∀m. m ≤ j)" "∃n. ¬ n ≤ i"  
  using Suc_n_not_le_n apply blast
 using Suc_n_not_le_n apply blast
 done
from th   show "(j<infinite∧i<infinite) ⟹ j<infinite∧(nrows(singleton_matrix j i e) = (if e = 0 then 0 else Suc j))"
apply (auto)
apply (rule le_antisym)
apply (subst nrows_le)
apply (simp add: singleton_matrix_def, auto)
apply (subst RepAbs_matrix)
apply auto
apply (simp add: Suc_le_eq)
apply (rule not_leE)
apply (subst nrows_le)
by simp
qed
(*
lemma ncols_singleton[simp]: "j<infinite∧i<infinite⟹ncols(singleton_matrix j i e) = (if e = 0 then 0 else Suc i)"
proof-
have th: "¬ (∀m. m ≤ j)" "∃n. ¬ n ≤ i" by arith+
from th show ?thesis 
apply (auto)
apply (rule le_antisym)
apply (subst ncols_le)
apply (simp add: singleton_matrix_def, auto)
apply (subst RepAbs_matrix)
apply auto
apply (simp add: Suc_le_eq)
sorry
apply (rule not_leE)
apply (subst ncols_le)
by simp
qed

lemma combine_singleton: "j<infinite∧i<infinite⟹f 0 0 = 0 ⟹ combine_matrix f (singleton_matrix j i a) (singleton_matrix j i b) = singleton_matrix j i (f a b)"
apply (simp add: singleton_matrix_def combine_matrix_def combine_infmatrix_def)
apply (subst RepAbs_matrix)
apply (rule exI[of _ "Suc j"], simp)
apply (rule exI[of _ "Suc i"], simp)
apply (rule comb[of "Abs_matrix" "Abs_matrix"], simp, (rule ext)+)
apply (subst RepAbs_matrix)
apply (rule exI[of _ "Suc j"], simp)
apply (rule exI[of _ "Suc i"], simp)
by simp

lemma transpose_singleton[simp]: "i<infinite∧j<infinite⟹transpose_matrix (singleton_matrix j i a) = singleton_matrix i j a"
apply (subst Rep_matrix_inject[symmetric], (rule ext)+)
apply (simp)
done*)
(*
lemma Rep_move_matrix[simp]:
  "Rep_matrix (move_matrix A y x) j i =
  (if (((int j)-y) < 0) | (((int i)-x) < 0) then 0 else Rep_matrix A (nat((int j)-y)) (nat((int i)-x)))"
apply (simp add: move_matrix_def)
apply (auto)
apply (subst RepAbs_matrix)
apply auto
apply(  rule exI[of _ "(nrows A)+(nat (abs y))"])
apply auto
sorry
by (subst RepAbs_matrix,
  rule exI[of _ "(nrows A)+(nat (abs y))"], auto, rule nrows, arith,
  rule exI[of _ "(ncols A)+(nat (abs x))"], auto, rule ncols, arith)+

lemma move_matrix_0_0[simp]: "move_matrix A 0 0 = A"
by (simp add: move_matrix_def)

lemma move_matrix_ortho: "move_matrix A j i = move_matrix (move_matrix A j 0) 0 i"
apply (subst Rep_matrix_inject[symmetric])
apply (rule ext)+
apply (simp)
done

lemma transpose_move_matrix[simp]:
  "transpose_matrix (move_matrix A x y) = move_matrix (transpose_matrix A) y x"
apply (subst Rep_matrix_inject[symmetric], (rule ext)+)
apply (simp)
done

lemma move_matrix_singleton[simp]: "move_matrix (singleton_matrix u v x) j i = 
  (if (j + int u < 0) | (i + int v < 0) then zero else (singleton_matrix (nat (j + int u)) (nat (i + int v)) x))"
  apply (subst Rep_matrix_inject[symmetric])
  apply (rule ext)+
  apply (case_tac "j + int u < 0")
  apply (simp, arith)
  apply (case_tac "i + int v < 0")
  apply (simp, arith)
  apply simp
  apply arith
  done

lemma Rep_take_columns[simp]:
  "Rep_matrix (take_columns A c) j i =
  (if i < c then (Rep_matrix A j i) else 0)"
apply (simp add: take_columns_def)
apply (simplesubst RepAbs_matrix)
apply (rule exI[of _ "nrows A"], auto, simp add: nrows_le)
apply (rule exI[of _ "ncols A"], auto, simp add: ncols_le)
done
*)
(*
lemma Rep_take_rows[simp]:
  "Rep_matrix (take_rows A r) j i =
  (if j < r then (Rep_matrix A j i) else 0)"
apply (simp add: take_rows_def)
apply (simplesubst RepAbs_matrix)
apply (rule exI[of _ "nrows A"], auto, simp add: nrows_le)
apply (rule exI[of _ "ncols A"], auto, simp add: ncols_le)
done

lemma Rep_column_of_matrix[simp]:
  "Rep_matrix (column_of_matrix A c) j i = (if i = 0 then (Rep_matrix A j c) else 0)"
  apply (simp add: column_of_matrix_def)
  sorry

lemma Rep_row_of_matrix[simp]:
  "Rep_matrix (row_of_matrix A r) j i = (if j = 0 then (Rep_matrix A r i) else 0)"
  by (simp add: row_of_matrix_def)

lemma column_of_matrix: "ncols A <= n ⟹ column_of_matrix A n = zero"
apply (subst Rep_matrix_inject[THEN sym])
apply (rule ext)+
by (simp add: ncols)

lemma row_of_matrix: "nrows A <= n ⟹ row_of_matrix A n = zero"
apply (subst Rep_matrix_inject[THEN sym])
apply (rule ext)+
by (simp add: nrows)

lemma mult_matrix_singleton_right[simp]:
  assumes
  "! x. fmul x 0 = 0"
  "! x. fmul 0 x = 0"
  "! x. fadd 0 x = x"
  "! x. fadd x 0 = x"
  shows "(mult_matrix fmul fadd A (singleton_matrix j i e)) = apply_matrix (% x. fmul x e) (move_matrix (column_of_matrix A j) 0 (int i))"
  apply (simp add: mult_matrix_def)
  apply (subst mult_matrix_nm[of _ _ _ "max (ncols A) (Suc j)"])
  apply (auto)
  apply (simp add: assms)+
  apply (simp add: mult_matrix_n_def apply_matrix_def apply_infmatrix_def)
  apply (rule comb[of "Abs_matrix" "Abs_matrix"], auto, (rule ext)+)
  apply (subst foldseq_almostzero[of _ j])
  apply (simp add: assms)+
  apply (auto)
  done

lemma mult_matrix_ext:
  assumes
  eprem:
  "? e. (! a b. a ≠ b ⟶ fmul a e ≠ fmul b e)"
  and fprems:
  "! a. fmul 0 a = 0"
  "! a. fmul a 0 = 0"
  "! a. fadd a 0 = a"
  "! a. fadd 0 a = a"
  and contraprems:
  "mult_matrix fmul fadd A = mult_matrix fmul fadd B"
  shows
  "A = B"
proof(rule contrapos_np[of "False"], simp)
  assume a: "A ≠ B"
  have b: "!! f g. (! x y. f x y = g x y) ⟹ f = g" by ((rule ext)+, auto)
  have "? j i. (Rep_matrix A j i) ≠ (Rep_matrix B j i)"
    apply (rule contrapos_np[of "False"], simp+)
    apply (insert b[of "Rep_matrix A" "Rep_matrix B"], simp)
    by (simp add: Rep_matrix_inject a)
  then obtain J I where c:"(Rep_matrix A J I) ≠ (Rep_matrix B J I)" by blast
  from eprem obtain e where eprops:"(! a b. a ≠ b ⟶ fmul a e ≠ fmul b e)" by blast
  let ?S = "singleton_matrix I 0 e"
  let ?comp = "mult_matrix fmul fadd"
  have d: "!!x f g. f = g ⟹ f x = g x" by blast
  have e: "(% x. fmul x e) 0 = 0" by (simp add: assms)
  have "~(?comp A ?S = ?comp B ?S)"
    apply (rule notI)
    apply (simp add: fprems eprops)
    apply (simp add: Rep_matrix_inject[THEN sym])
    apply (drule d[of _ _ "J"], drule d[of _ _ "0"])
    by (simp add: e c eprops)
  with contraprems show "False" by simp
qed
*)
definition foldmatrix :: "(real ⇒real ⇒ real) ⇒ (real ⇒real ⇒real) ⇒ ( infmatrix) ⇒ nat ⇒ nat ⇒ real" where
  "foldmatrix f g A m n == foldseq_transposed g (% j. foldseq f (A j) n) m"

definition foldmatrix_transposed :: "(real ⇒real ⇒ real) ⇒ (real ⇒real ⇒ real) ⇒ ( infmatrix) ⇒ nat ⇒ nat ⇒real" where
  "foldmatrix_transposed f g A m n == foldseq g (% j. foldseq_transposed f (A j) n) m"

lemma foldmatrix_transpose:
  assumes
  "! a b c d. g(f a b) (f c d) = f (g a c) (g b d)"
  shows
  "foldmatrix f g A m n = foldmatrix_transposed g f (transpose_infmatrix A) n m"
proof -
  have forall:"!! P x. (! x. P x) ⟹ P x" by auto
  have tworows:"! A. foldmatrix f g A 1 n = foldmatrix_transposed g f (transpose_infmatrix A) n 1"
    apply (induct n)
    apply (simp add: foldmatrix_def foldmatrix_transposed_def assms)+
    apply (auto)
    by (drule_tac x="(% j i. A j (Suc i))" in forall, simp)
  show "foldmatrix f g A m n = foldmatrix_transposed g f (transpose_infmatrix A) n m"
    apply (simp add: foldmatrix_def foldmatrix_transposed_def)
    apply (induct m, simp)
    apply (simp)
    apply (insert tworows)
    apply (drule_tac x="% j i. (if j = 0 then (foldseq_transposed g (λu. A u i) m) else (A (Suc m) i))" in spec)
    by (simp add: foldmatrix_def foldmatrix_transposed_def)
qed

lemma foldseq_foldseq:
assumes
  "associative f"
  "associative g"
  "! a b c d. g(f a b) (f c d) = f (g a c) (g b d)"
shows
  "foldseq g (% j. foldseq f (A j) n) m = foldseq f (% j. foldseq g ((transpose_infmatrix A) j) m) n"
  apply (insert foldmatrix_transpose[of g f A m n])
  by (simp add: foldmatrix_def foldmatrix_transposed_def foldseq_assoc[THEN sym] assms)

lemma mult_n_nrows:
assumes
"! a. fmul 0 a = 0"
"! a. fmul a 0 = 0"
"fadd 0 0 = 0"
shows "nrows (mult_matrix_n n fmul fadd A B) ≤ nrows A"
apply (subst nrows_le)
apply (simp add: mult_matrix_n_def)
apply (subst RepAbs_matrix)
apply (rule_tac x="nrows A" in exI)
apply (simp add: nrows assms foldseq_zero)
apply (rule_tac x="ncols B" in exI)
apply (simp add: ncols assms foldseq_zero)
apply (simp add: nrows assms foldseq_zero)
done

lemma mult_n_ncols:
assumes
"! a. fmul 0 a = 0"
"! a. fmul a 0 = 0"
"fadd 0 0 = 0"
shows "ncols (mult_matrix_n n fmul fadd A B) ≤ ncols B"
apply (subst ncols_le)
apply (simp add: mult_matrix_n_def)
apply (subst RepAbs_matrix)
apply (rule_tac x="nrows A" in exI)
apply (simp add: nrows assms foldseq_zero)
apply (rule_tac x="ncols B" in exI)
apply (simp add: ncols assms foldseq_zero)
apply (simp add: ncols assms foldseq_zero)
done

lemma mult_nrows:
assumes
"! a. fmul 0 a = 0"
"! a. fmul a 0 = 0"
"fadd 0 0 = 0"
shows "nrows (mult_matrix fmul fadd A B) ≤ nrows A"
by (simp add: mult_matrix_def mult_n_nrows assms)

lemma mult_ncols:
assumes
"! a. fmul 0 a = 0"
"! a. fmul a 0 = 0"
"fadd 0 0 = 0"
shows "ncols (mult_matrix fmul fadd A B) ≤ ncols B"
by (simp add: mult_matrix_def mult_n_ncols assms)
(*
lemma nrows_move_matrix_le: "nrows (move_matrix A j i) <= nat((int (nrows A)) + j)"
  apply (auto simp add: nrows_le)
  apply (rule nrows)
  apply (arith)
  done

lemma ncols_move_matrix_le: "ncols (move_matrix A j i) <= nat((int (ncols A)) + i)"
  apply (auto simp add: ncols_le)
  apply (rule ncols)
  apply (arith)
  done
*)
lemma mult_matrix_assoc:
  assumes
  "! a. fmul1 0 a = 0"
  "! a. fmul1 a 0 = 0"
  "! a. fmul2 0 a = 0"
  "! a. fmul2 a 0 = 0"
  "fadd1 0 0 = 0"
  "fadd2 0 0 = 0"
  "! a b c d. fadd2 (fadd1 a b) (fadd1 c d) = fadd1 (fadd2 a c) (fadd2 b d)"
  "associative fadd1"
  "associative fadd2"
  "! a b c. fmul2 (fmul1 a b) c = fmul1 a (fmul2 b c)"
  "! a b c. fmul2 (fadd1 a b) c = fadd1 (fmul2 a c) (fmul2 b c)"
  "! a b c. fmul1 c (fadd2 a b) = fadd2 (fmul1 c a) (fmul1 c b)"
  shows "mult_matrix fmul2 fadd2 (mult_matrix fmul1 fadd1 A B) C = mult_matrix fmul1 fadd1 A (mult_matrix fmul2 fadd2 B C)"
proof -
  have comb_left:  "!! A B x y. A = B ⟹ (Rep_matrix (Abs_matrix A)) x y = (Rep_matrix(Abs_matrix B)) x y" by blast
  have fmul2fadd1fold: "!! x s n. fmul2 (foldseq fadd1 s n)  x = foldseq fadd1 (% k. fmul2 (s k) x) n"
    by (rule_tac g1 = "% y. fmul2 y x" in ssubst [OF foldseq_distr_unary], insert assms, simp_all)
  have fmul1fadd2fold: "!! x s n. fmul1 x (foldseq fadd2 s n) = foldseq fadd2 (% k. fmul1 x (s k)) n"
    using assms by (rule_tac g1 = "% y. fmul1 x y" in ssubst [OF foldseq_distr_unary], simp_all)
  let ?N = "max (ncols A) (max (ncols B) (max (nrows B) (nrows C)))"
  show ?thesis
    apply (simp add: Rep_matrix_inject[THEN sym])
    apply (rule ext)+
    apply (simp add: mult_matrix_def)
    apply (simplesubst mult_matrix_nm[of _ "max (ncols (mult_matrix_n (max (ncols A) (nrows B)) fmul1 fadd1 A B)) (nrows C)" _ "max (ncols B) (nrows C)"])
    apply (simp add: max1 max2 mult_n_ncols mult_n_nrows assms)+
    apply (simplesubst mult_matrix_nm[of _ "max (ncols A) (nrows (mult_matrix_n (max (ncols B) (nrows C)) fmul2 fadd2 B C))" _ "max (ncols A) (nrows B)"])
    apply (simp add: max1 max2 mult_n_ncols mult_n_nrows assms)+
    apply (simplesubst mult_matrix_nm[of _ _ _ "?N"])
    apply (simp add: max1 max2 mult_n_ncols mult_n_nrows assms)+
    apply (simplesubst mult_matrix_nm[of _ _ _ "?N"])
    apply (simp add: max1 max2 mult_n_ncols mult_n_nrows assms)+
    apply (simplesubst mult_matrix_nm[of _ _ _ "?N"])
    apply (simp add: max1 max2 mult_n_ncols mult_n_nrows assms)+
    apply (simplesubst mult_matrix_nm[of _ _ _ "?N"])
    apply (simp add: max1 max2 mult_n_ncols mult_n_nrows assms)+
    apply (simp add: mult_matrix_n_def)
    apply (rule comb_left)
    apply ((rule ext)+, simp)
    apply (simplesubst RepAbs_matrix)
    apply (rule exI[of _ "nrows B"])
    apply (simp add: nrows assms foldseq_zero)
    apply (rule exI[of _ "ncols C"])
    apply (simp add: assms ncols foldseq_zero)
    apply (subst RepAbs_matrix)
    apply (rule exI[of _ "nrows A"])
    apply (simp add: nrows assms foldseq_zero)
    apply (rule exI[of _ "ncols B"])
    apply (simp add: assms ncols foldseq_zero)
    apply (simp add: fmul2fadd1fold fmul1fadd2fold assms)
    apply (subst foldseq_foldseq)
    apply (simp add: assms)+
    apply (simp add: transpose_infmatrix)
    done
qed

lemma
  assumes
  "! a. fmul1 0 a = 0"
  "! a. fmul1 a 0 = 0"
  "! a. fmul2 0 a = 0"
  "! a. fmul2 a 0 = 0"
  "fadd1 0 0 = 0"
  "fadd2 0 0 = 0"
  "! a b c d. fadd2 (fadd1 a b) (fadd1 c d) = fadd1 (fadd2 a c) (fadd2 b d)"
  "associative fadd1"
  "associative fadd2"
  "! a b c. fmul2 (fmul1 a b) c = fmul1 a (fmul2 b c)"
  "! a b c. fmul2 (fadd1 a b) c = fadd1 (fmul2 a c) (fmul2 b c)"
  "! a b c. fmul1 c (fadd2 a b) = fadd2 (fmul1 c a) (fmul1 c b)"
  shows
  "(mult_matrix fmul1 fadd1 A) o (mult_matrix fmul2 fadd2 B) = mult_matrix fmul2 fadd2 (mult_matrix fmul1 fadd1 A B)"
apply (rule ext)+
apply (simp add: comp_def )
apply (simp add: mult_matrix_assoc assms)
done

lemma mult_matrix_assoc_simple:
  assumes
  "! a. fmul 0 a = 0"
  "! a. fmul a 0 = 0"
  "fadd 0 0 = 0"
  "associative fadd"
  "commutative fadd"
  "associative fmul"
  "distributive fmul fadd"
  shows "mult_matrix fmul fadd (mult_matrix fmul fadd A B) C = mult_matrix fmul fadd A (mult_matrix fmul fadd B C)"
proof -
  have "!! a b c d. fadd (fadd a b) (fadd c d) = fadd (fadd a c) (fadd b d)"
    using assms by (simp add: associative_def commutative_def)
  then show ?thesis
    apply (subst mult_matrix_assoc)
    using assms
    apply simp_all
    apply (simp_all add: associative_def distributive_def l_distributive_def r_distributive_def)
    done
qed

lemma transpose_apply_matrix: "f 0 = 0 ⟹ transpose_matrix (apply_matrix f A) = apply_matrix f (transpose_matrix A)"
apply (simp add: Rep_matrix_inject[THEN sym])
apply (rule ext)+
by simp

lemma transpose_combine_matrix: "f 0 0 = 0 ⟹ transpose_matrix (combine_matrix f A B) = combine_matrix f (transpose_matrix A) (transpose_matrix B)"
apply (simp add: Rep_matrix_inject[THEN sym])
apply (rule ext)+
by simp

lemma Rep_mult_matrix:
  assumes
  "! a. fmul 0 a = 0"
  "! a. fmul a 0 = 0"
  "fadd 0 0 = 0"
  shows
  "Rep_matrix(mult_matrix fmul fadd A B) j i =
  foldseq fadd (% k. fmul (Rep_matrix A j k) (Rep_matrix B k i)) (max (ncols A) (nrows B))"
apply (simp add: mult_matrix_def mult_matrix_n_def)
apply (subst RepAbs_matrix)
apply (rule exI[of _ "nrows A"], insert assms, simp add: nrows foldseq_zero)
apply (rule exI[of _ "ncols B"], insert assms, simp add: ncols foldseq_zero)
apply simp
done

lemma transpose_mult_matrix:
  assumes
  "! a. fmul 0 a = 0"
  "! a. fmul a 0 = 0"
  "fadd 0 0 = 0"
  "! x y. fmul y x = fmul x y"
  shows
  "transpose_matrix (mult_matrix fmul fadd A B) = mult_matrix fmul fadd (transpose_matrix B) (transpose_matrix A)"
  apply (simp add: Rep_matrix_inject[THEN sym])
  apply (rule ext)+
  using assms
  apply (simp add: Rep_mult_matrix ac_simps)
  done
(*
lemma column_transpose_matrix: "column_of_matrix (transpose_matrix A) n = transpose_matrix (row_of_matrix A n)"
apply (simp add:  Rep_matrix_inject[THEN sym])
apply (rule ext)+
by simp

lemma take_columns_transpose_matrix: "take_columns (transpose_matrix A) n = transpose_matrix (take_rows A n)"
apply (simp add: Rep_matrix_inject[THEN sym])
apply (rule ext)+
sledgehammer
by simp
*)

definition matplus::"matrix⇒matrix⇒matrix" where
   "matplus A B = combine_matrix (op +) A B"
definition minus_matrix::"matrix⇒matrix" where
  "minus_matrix A = apply_matrix uminus A"
definition diff_matrix::"matrix⇒matrix⇒matrix" where
  "diff_matrix A  B = combine_matrix (op -) A B"
definition times_matrix::"matrix⇒matrix⇒matrix" where
  "times_matrix A  B = mult_matrix (op *) (op +) A B"
definition Tr::"matrix⇒real" where
  "Tr A   = tr (op +)  A "
definition trace::"matrix⇒real" where
"trace A=foldseq_transposed (op +) (%k. Rep_matrix A k k) (max (nrows A) (ncols A)) "
definition rows_sum_pow::"matrix⇒nat⇒real"where
"rows_sum_pow A i=foldseq (op +) (%k. Rep_matrix A i k*Rep_matrix A i k) (ncols A)"
definition all_sum_pow::"matrix⇒real"where
"all_sum_pow A =foldseq (op +) (%k. rows_sum_pow A k) (nrows A)"

definition timematrix::"matrix⇒matrix⇒matrix" where
 "timematrix A  B = mult_matrix1 (op *) (op +) A B"
lemma eql:"Tr A=trace A"
apply(simp add:Tr_def tr_def trace_def)
by (simp add: associative_def foldseq_assoc)
lemma eql1:"times_matrix A B=timematrix A B"
apply(simp add:times_matrix_def mult_matrix_def timematrix_def mult_matrix_def mult_matrix_n_def mult_matrix1_def)
apply(simp add:mult_matrix_n1_def)
by (simp add: associative_def foldseq_assoc)
(*A+B=B+A*)
lemma a:"matplus A B=matplus B A"
 apply (simp add: matplus_def)
apply (rule combine_matrix_commute[simplified commutative_def, THEN spec, THEN spec])
 apply (simp_all add: add.commute)
 done
 (*(a+b)+c=a+(b+c)*)
lemma b:"matplus (matplus A B) C=matplus A (matplus B C)"
 apply (simp add: matplus_def)
 apply (rule combine_matrix_assoc[simplified associative_def, THEN spec, THEN spec, THEN spec])
 apply (simp_all add: add.assoc)
 done
(*  (m1*m2)*m3=m1*(m2*m3)   *)
lemma d:"times_matrix (times_matrix A B) C=times_matrix A (times_matrix B C)"
apply (simp add: times_matrix_def)
apply (rule mult_matrix_assoc)
apply (simp_all add: associative_def algebra_simps)
done
 (*(a+b)*c=ac+bc*)
lemma e:"times_matrix (matplus A B) C=matplus (times_matrix A C) (times_matrix B C) "
 apply (simp add: times_matrix_def matplus_def)
 apply (rule l_distributive_matrix[simplified l_distributive_def, THEN spec,   THEN spec, THEN spec])
 apply (simp_all add: associative_def commutative_def algebra_simps)
 done
 (*  c(a+b) =ca+cb       *)
 lemma f:"times_matrix A (matplus B C) =matplus (times_matrix A B) (times_matrix A C) "
 apply (simp add: times_matrix_def matplus_def)
 apply (rule r_distributive_matrix[simplified r_distributive_def, THEN spec, THEN spec, THEN spec])
 apply (simp_all add: associative_def commutative_def algebra_simps)
 done
  (*  0+a=a    *)
 lemma g:"matplus zero A=A"
  apply (simp add: matplus_def)
  apply(simp add:combine_matrix_def combine_infmatrix_def)
  done
  (*  0+a=a    *)
 lemma gg:"matplus A zero=A"
  apply (simp add: matplus_def)
  apply(simp add:combine_matrix_def combine_infmatrix_def)
  done

  (*  0+a=a    *)
  lemma h:"matplus A zero =A"
  apply (simp add: matplus_def)
  apply(simp add:combine_matrix_def combine_infmatrix_def)
  done
 definition scalar_mult :: "real ⇒  matrix ⇒  matrix" where
  "scalar_mult a m == apply_matrix (op * a) m"
 lemma j:"minus_matrix A=scalar_mult (-1) A"
 apply(simp add:minus_matrix_def scalar_mult_def)
by (metis mult_minus1)
lemma kk:"Rep_matrix (minus_matrix A) i j=-(Rep_matrix A i j)"
by (simp add: minus_matrix_def)
lemma kkk:"(ncols (apply_matrix uminus A)) =ncols A"
apply(simp add:ncols_def)
apply auto
apply (simp add: nonzero_positions_def)
apply (simp add: nonzero_positions_def)
apply (simp add: nonzero_positions_def)
done

lemma k:"times_matrix ( minus_matrix A) B  =minus_matrix (times_matrix A B)"
apply(simp add:times_matrix_def )
apply(subst Rep_matrix_inject[symmetric])
apply(rule ext)+
apply(simp add:kk)
apply (simp add: times_matrix_def Rep_mult_matrix)
apply(simp add:minus_matrix_def)
apply(simp add:kkk)
by (simp add: foldseq_distr_unary)
lemma k_dual:"times_matrix c (minus_matrix b) =minus_matrix (times_matrix c b)"
apply(simp add:times_matrix_def )
apply(subst Rep_matrix_inject[symmetric])
apply(rule ext)+
apply(simp add:kk)
apply (simp add: times_matrix_def Rep_mult_matrix)
apply(simp add:minus_matrix_def)
apply(subgoal_tac "(nrows (apply_matrix uminus b)) =nrows b",auto)
apply (simp add: foldseq_distr_unary)
apply(simp add:nrows_def)
apply auto
apply (metis equals0D kkk nat.distinct(1) ncols_def)
apply (metis equals0D kkk ncols_def old.nat.distinct(2))
by (simp add: nonzero_positions_def)
(*a+(-b) =a-b*)
lemma l:"matplus A (minus_matrix B) =diff_matrix A B"
 by (simp add: matplus_def diff_matrix_def minus_matrix_def Rep_matrix_inject [symmetric] ext)
lemma ll:"minus_matrix (matplus A B) =matplus (minus_matrix A) (minus_matrix B)"
apply(simp add:j scalar_mult_def)
apply(simp add:matplus_def)
apply(simp add:combine_matrix_def)
apply (simp add: Rep_matrix_inject[THEN sym])
apply (rule ext)+
apply auto
done


 (* (a-b)*c=a*c-b*c    *)
 lemma i:"times_matrix (diff_matrix A B) C=diff_matrix (times_matrix A C) (times_matrix B C) "
apply(subgoal_tac "times_matrix (matplus A (minus_matrix B)) C=diff_matrix (times_matrix A C) (times_matrix B C)")
apply(simp add:l)
apply(simp add:e)
apply(subgoal_tac " matplus (times_matrix A C) (times_matrix (minus_matrix B) C) = matplus (times_matrix A C) (minus_matrix (times_matrix B C)) ")
apply(simp add:l)
apply(simp add:k)
done
lemma m:"diff_matrix A A=zero"
apply(simp add:diff_matrix_def )
apply(simp add:Rep_matrix_inject[symmetric])
apply(rule ext)+
apply auto
done

lemma q:"Tr (matplus A B) =(Tr A) + (Tr B)"
apply(simp add:Tr_def tr_def)
apply(subgoal_tac "max (max (nrows (matplus A B)) (ncols (matplus A B)))  (max (max (nrows B) (ncols B)) (max (nrows A) (ncols A))) ≥(max (nrows B) (ncols B))")
prefer 2
using max.cobounded1 max.coboundedI2 apply blast
apply(subgoal_tac "foldseq op + (λk. Rep_matrix B k k) (max (nrows B) (ncols B)) =
  foldseq op + (λk. Rep_matrix B k k) (max (max (nrows (matplus A B)) (ncols (matplus A B))) 
  (max (max (nrows B) (ncols B)) (max (nrows A) (ncols A))))")
prefer 2
apply (simp add: foldseq_zerotail ncols)
apply(subgoal_tac "max (max (nrows (matplus A B)) (ncols (matplus A B)))  (max (max (nrows B) (ncols B)) (max (nrows A) (ncols A)))
  ≥(max (nrows A) (ncols A))")
prefer 2
apply (simp add: le_max_iff_disj)
apply(subgoal_tac "foldseq op + (λk. Rep_matrix A k k) (max (nrows A) (ncols A)) =
  foldseq op + (λk. Rep_matrix A k k) (max (max (nrows (matplus A B)) (ncols (matplus A B))) 
  (max (max (nrows B) (ncols B)) (max (nrows A) (ncols A))))")
prefer 2
apply (simp add: foldseq_zerotail ncols)
apply(subgoal_tac "max (max (nrows (matplus A B)) (ncols (matplus A B)))  (max (max (nrows B) (ncols B)) (max (nrows A) (ncols A)))
  ≥(max (nrows (matplus A B)) (ncols (matplus A B)))")
prefer 2
using max.cobounded1 apply blast
apply(subgoal_tac " foldseq op + (λk. Rep_matrix (matplus A B) k k) (max (nrows (matplus A B)) (ncols (matplus A B))) =
  foldseq op + (λk. Rep_matrix (matplus A B) k k) (max (max (nrows (matplus A B)) (ncols (matplus A B))) 
  (max (max (nrows B) (ncols B)) (max (nrows A) (ncols A))))")
prefer 2
apply (simp add: foldseq_zerotail ncols)
apply(subgoal_tac " foldseq op + (λk. Rep_matrix (matplus A B) k k) (max (max (nrows (matplus A B)) (ncols (matplus A B))) 
  (max (max (nrows B) (ncols B)) (max (nrows A) (ncols A)))) =
    foldseq op + (λk. Rep_matrix A k k) (max (max (nrows (matplus A B)) (ncols (matplus A B))) 
  (max (max (nrows B) (ncols B)) (max (nrows A) (ncols A)))) + foldseq op + (λk. Rep_matrix B k k) (max (max (nrows (matplus A B)) (ncols (matplus A B))) 
  (max (max (nrows B) (ncols B)) (max (nrows A) (ncols A)))) ")
apply simp
apply(simp add:matplus_def)
apply(rule  foldseq_distr)
using add.assoc associative_def apply blast
using add.commute commutative_def by blast


definition
  one_matrix  where
  "one_matrix  = Abs_matrix (% j i. if j = i & j < infinite then 1 else 0)"
  lemma Rep_one_matrix: "Rep_matrix (one_matrix ) j i = (if (j = i & j < infinite) then 1 else 0)"
unfolding one_matrix_def
apply (simplesubst RepAbs_matrix)
apply (meson not_less order_refl)
apply (metis le_neq_implies_less less_asym order_refl)
by blast

lemma nrows_one_matrix[simp]: "nrows ((one_matrix )) = infinite" (is "?r = _")
proof -
  have "?r <= infinite" by simp 
  moreover have "infinite <= ?r" 
  apply(simp add:le_nrows)
   by (metis (full_types) Rep_one_matrix not_less numeral_One order_refl zero_neq_numeral)
  ultimately show "?r = infinite" 
using antisym_conv by blast
qed

lemma ncols_one_matrix[simp]: "ncols ((one_matrix )) = infinite" (is "?r = _")
proof -
  have "?r <= infinite"  by simp 
  moreover have "infinite <= ?r" 
  apply(simp add:le_ncols)
by (metis Rep_one_matrix nrows_le nrows_one_matrix)
  ultimately show "?r = infinite"using antisym_conv by blast
qed
 lemma one_matrix_mult_right[simp]: "  times_matrix A  (one_matrix ) = A"
apply (subst Rep_matrix_inject[THEN sym])
apply (rule ext)+
apply (simp add: times_matrix_def Rep_mult_matrix)
apply (rule_tac j1="xa" in ssubst[OF foldseq_almostzero])
apply (simp_all)
using Rep_one_matrix apply presburger
by (metis (no_types, lifting) Rep_one_matrix le_less max2 max_def ncols ncols_max)

definition one_matrix1_def: "I = one_matrix "
lemma n:"times_matrix  I A=A"
apply(simp add: one_matrix1_def)
apply (subst Rep_matrix_inject[THEN sym])
apply (rule ext)+
apply (simp add: times_matrix_def Rep_mult_matrix )
apply (rule_tac j1="x" in ssubst[OF foldseq_almostzero])
apply (simp_all)
prefer 2
apply (metis (no_types, lifting) Rep_one_matrix le_less max2 max_def nrows nrows_max)
using Rep_one_matrix apply presburger
done

type_synonym Mat="matrix"
definition mat_add::"matrix⇒matrix⇒matrix" where
   "mat_add A B = matplus A B"
definition mat_mult::"matrix⇒matrix⇒matrix" where
   "mat_mult A B = times_matrix A B"
definition mat_sub::"matrix⇒matrix⇒matrix" where
   "mat_sub A B = diff_matrix A B"
   
lemma eql2:"mat_mult A B=timematrix A B"
using eql1 mat_mult_def by auto
(*(a+b)*c=a*c+b*c    *)
lemma mult_allo1:"mat_mult (mat_add a b) c=mat_add  (mat_mult a c)  (mat_mult b c)"
using e mat_add_def mat_mult_def by auto
(* (a-b)*c=a*c-b*c     *)
lemma mult_sub_allo1:"mat_mult (mat_sub a b) c=mat_sub (mat_mult a c) (mat_mult b c)" 
by (simp add: i mat_mult_def mat_sub_def)
(* c*(a-b)=c*a-b*c     *)
lemma mult_sub_allo2:"mat_mult c (mat_sub a b) =mat_sub (mat_mult c a) (mat_mult c b)" 
apply(subgoal_tac "mat_sub a b=mat_add a (minus_matrix b)")
prefer 2
apply (simp add: l mat_add_def mat_sub_def,auto)
apply(subgoal_tac " mat_sub (mat_mult c a) (mat_mult c b) =mat_add (mat_mult c a) (minus_matrix (mat_mult c b))")
prefer 2
apply (simp add: l mat_add_def mat_sub_def,auto)
apply(subgoal_tac "(minus_matrix (mat_mult c b)) =mat_mult c (minus_matrix b)",auto)
apply (simp add: f mat_add_def mat_mult_def)
using k_dual mat_mult_def by auto
(*  c(a+b) =ca+cb        *)
lemma mult_allo2:"mat_mult c (mat_add a b) =mat_add (mat_mult c a )  (mat_mult c b)"
by (simp add: f mat_add_def mat_mult_def)
(*a-a=0      *)
lemma sub_self:"mat_sub a a=zero"
by (simp add: m mat_sub_def)
(* a+0=0 *)
lemma zero_add:"mat_add a zero=a"
by (simp add: gg mat_add_def)
(*a-0=a*)
lemma zero_sub:"mat_sub a zero=a"
by (metis a l m mat_add_def mat_sub_def zero_add)
(* a*0=0  *)
lemma zero_mult_r:"mat_mult a zero=zero"
by (simp add: mat_mult_def times_matrix_def)
(*0*a=0*)
lemma zero_mult_l:"mat_mult zero b=zero"
by (simp add: mat_mult_def times_matrix_def)
lemma sub_add:"mat_add a (minus_matrix b)=mat_sub a  b"
by (simp add: l mat_add_def mat_sub_def)

(* Tr (a+b) =Tr a+Tr b  *)
lemma tr_allo:"Tr (mat_add a b) =Tr a+Tr b"
using mat_add_def q by auto
(*  (m1*m2)*m3=m1*(m2*m3)   OK *)
lemma mult_exchange:"mat_mult (mat_mult m1 m2) m3=mat_mult m1 (mat_mult m2 m3)"
by (simp add: d mat_mult_def)
lemma zero_tr:"Tr zero=0"
apply(simp add:Tr_def tr_def)
done

(*Tr (a-b) =Tr a - Tr b*)
lemma tr_allo1:"Tr (mat_sub a b) =Tr a -Tr b"
apply(subgoal_tac "Tr (mat_add a (minus_matrix b)) =Tr a - Tr b ")
apply (simp add: l mat_add_def mat_sub_def)
apply(subgoal_tac " Tr a - Tr b =Tr a + Tr (minus_matrix b)")
apply (simp add: tr_allo)
apply(simp add:minus_matrix_def Tr_def)
by (metis Tr_def add.commute add.left_neutral diff_eq_eq l m mat_add_def minus_matrix_def tr_allo uminus_add_conv_diff zero_tr)
(*I*a=a*)
lemma Ident:"mat_mult I a=a"
apply(simp add:mat_mult_def)
apply(simp add:n)
done
lemma Ident_dual:"mat_mult a I=a"
by (simp add: mat_mult_def one_matrix1_def)


lemma transpose_matrix_mult: "transpose_matrix (mat_mult A B) =mat_mult (transpose_matrix B)  (transpose_matrix A)"
apply (simp add: mat_mult_def times_matrix_def)
apply (subst transpose_mult_matrix)
apply (simp_all add: mult.commute)
done
lemma transpose_matrix_add: "transpose_matrix (mat_add A B) = mat_add (transpose_matrix A)  (transpose_matrix B)"
apply (simp add: mat_add_def)
apply(simp add:matplus_def)
by (simp add: transpose_combine_matrix)

lemma transpose_matrix_diff: "transpose_matrix (mat_sub A B) = mat_sub (transpose_matrix A)  (transpose_matrix B)"
by (simp add: mat_sub_def diff_matrix_def transpose_combine_matrix)

lemma transpose_matrix_minus: "transpose_matrix (minus_matrix A) = minus_matrix (transpose_matrix A)"
by (simp add: minus_matrix_def transpose_apply_matrix)
(*    M†   *)
definition dag::"Mat⇒Mat" where
"dag A=transpose_matrix A"
lemma dag_dag:"dag (dag A) =A"
using dag_def by auto
lemma dag_mult:"dag (mat_mult A B) =mat_mult (dag B) (dag A)"
apply(simp add:dag_def)
apply(simp add:transpose_matrix_mult)
done
lemma dag_zero:"dag zero=zero"
apply (simp add:dag_def)
done
lemma dag_I:"dag I=I"
apply(simp add:dag_def)
by (metis mat_mult_def n transpose_matrix_mult transpose_transpose_id)
(*  Tr a=Tr (dag a) *)
lemma tranpose_tr:"Tr A=Tr (dag A)"
apply(simp add:Tr_def tr_def dag_def)
by (simp add: max.commute)
lemma mult_nrow:"nrows (mat_mult a b) ≤nrows a"
by (simp add: mat_mult_def mult_nrows times_matrix_def)
lemma mult_ncol:"ncols (mat_mult a b) ≤ncols b"
by (simp add: mat_mult_def mult_matrix_def mult_n_ncols times_matrix_def)
definition Max::"nat⇒nat⇒nat⇒nat⇒nat" where
"Max a b c d=max (max (max a b) c) d"

lemma exchange_aux1:" foldseq_transposed op + (λk. Rep_matrix (times_matrix a b) k k) (max (nrows (times_matrix a b)) (ncols (times_matrix a b))) =
foldseq_transposed op + (λk. Rep_matrix (times_matrix a b) k k)  
  (Max (nrows a) (ncols a) (nrows b) (ncols b))"
apply(subgoal_tac "(max (nrows (times_matrix a b)) (ncols (times_matrix a b)))≤ (Max (nrows a) (ncols a) (nrows b) (ncols b))")
apply (simp add: foldseq_zerotail ncols)
apply(simp add:Max_def)
prefer 2
using Matrix.Max_def max1 max2 mult_ncols mult_nrows times_matrix_def apply auto[1]
proof -
have a:"foldseq op + (λk. Rep_matrix (times_matrix a b) k k) (max (nrows (times_matrix a b)) (ncols (times_matrix a b))) =
    foldseq op + (λk. Rep_matrix (times_matrix a b) k k) (max (max (max (nrows a) (ncols a)) (nrows b)) (ncols b))"
  apply(rule foldseq_zerotail,auto)
  apply (simp add: nrows)
  using mat_mult_def max1 mult_nrow apply auto[1]
  using mat_mult_def max2 mult_ncol by auto
  show " foldseq_transposed op + (λk. Rep_matrix (times_matrix a b) k k) (max (nrows (times_matrix a b)) (ncols (times_matrix a b))) =
    foldseq_transposed op + (λk. Rep_matrix (times_matrix a b) k k) (max (max (max (nrows a) (ncols a)) (nrows b)) (ncols b)) "
proof -
  have "∀f. (∃r ra rb. f (f (r∷real) ra) rb ≠ f r (f ra rb)) ∨ foldseq f = foldseq_transposed f"
    by (metis (full_types) associative_def foldseq_assoc)
  then obtain rr :: "(real ⇒ real ⇒ real) ⇒ real" and rra :: "(real ⇒ real ⇒ real) ⇒ real" and rrb :: "(real ⇒ real ⇒ real) ⇒ real" where
    "∀f. f (f (rr f) (rra f)) (rrb f) ≠ f (rr f) (f (rra f) (rrb f)) ∨ foldseq f = foldseq_transposed f"
    by metis
  thus ?thesis
    using local.a by force
   qed
qed

lemma exchange_aux11:" foldseq_transposed op + (λk. Rep_matrix (timematrix a b) k k) (max (nrows (timematrix a b)) (ncols (timematrix a b))) =
foldseq_transposed op + (λk. Rep_matrix (timematrix a b) k k)  
  (Max (nrows a) (ncols a) (nrows b) (ncols b))"
apply(subgoal_tac "(max (nrows (times_matrix a b)) (ncols (times_matrix a b)))≤ (Max (nrows a) (ncols a) (nrows b) (ncols b))")
apply (simp add: foldseq_zerotail ncols)
apply(simp add:Max_def)
prefer 2
using Matrix.Max_def max1 max2 mult_ncols mult_nrows times_matrix_def apply auto[1]
proof -
 have a:"foldseq op + (λk. Rep_matrix (timematrix a b) k k) (max (nrows (timematrix a b)) (ncols (timematrix a b))) =
    foldseq op + (λk. Rep_matrix (timematrix a b) k k) (max (max (max (nrows a) (ncols a)) (nrows b)) (ncols b)) "
    apply(rule foldseq_zerotail,auto)
  apply (simp add: nrows)
using eql2 max1 mult_nrow apply auto[1]
using eql2 max2 mult_ncol by auto
show " foldseq_transposed op + (λk. Rep_matrix (timematrix a b) k k) (max (nrows (timematrix a b)) (ncols (timematrix a b))) =
    foldseq_transposed op + (λk. Rep_matrix (timematrix a b) k k) (max (max (max (nrows a) (ncols a)) (nrows b)) (ncols b))"
proof -
  have "∀f. (∃r ra rb. f (f (r∷real) ra) rb ≠ f r (f ra rb)) ∨ foldseq f = foldseq_transposed f"
    by (metis (full_types) associative_def foldseq_assoc)
  then obtain rr :: "(real ⇒ real ⇒ real) ⇒ real" and rra :: "(real ⇒ real ⇒ real) ⇒ real" and rrb :: "(real ⇒ real ⇒ real) ⇒ real" where
    "∀f. f (f (rr f) (rra f)) (rrb f) ≠ f (rr f) (f (rra f) (rrb f)) ∨ foldseq f = foldseq_transposed f"
    by metis
  thus ?thesis
    using local.a by force
   qed
qed  
 lemma exchange_aux2:"mult_matrix_n (max (ncols a) (nrows b)) op * op + a b=
              mult_matrix_n ( (Max (nrows a) (ncols a) (nrows b) (ncols b))) op * op + a b"
        apply(simp add:Max_def)
        by (simp add: mult_matrix_nm)

lemma exchange_aux4:"
     Rep_matrix
     (Abs_matrix (λj i. foldseq op + (λka. Rep_matrix a j ka * Rep_matrix b ka i) (Matrix.Max (nrows a) (ncols a) (nrows b) (ncols b))))
       =
   (λj i. foldseq op + (λka. Rep_matrix a j ka * Rep_matrix b ka i) (Matrix.Max (nrows a) (ncols a) (nrows b) (ncols b))) "
     apply(rule RepAbs_matrix)
     apply(rule_tac x=" (max (nrows a) (ncols a))" in exI)
     apply (simp add: foldseq_zero nrows)
     apply(rule_tac x=" (max (nrows b) (ncols b))" in exI)
     apply (simp add: foldseq_zero ncols)
     done
 lemma exchange_aux5:"
     Rep_matrix
     (Abs_matrix (λj i. foldseq op + (λka. Rep_matrix b j ka * Rep_matrix a ka i) (Matrix.Max (nrows a) (ncols a) (nrows b) (ncols b))))
       =
   (λj i. foldseq op + (λka. Rep_matrix b j ka * Rep_matrix a ka i) (Matrix.Max (nrows a) (ncols a) (nrows b) (ncols b))) "
     apply(rule RepAbs_matrix)
     apply(rule_tac x=" (max (nrows b) (ncols b))" in exI)
     apply (simp add: foldseq_zero nrows)
     apply(rule_tac x=" (max (nrows a) (ncols a))" in exI)
     apply (simp add: foldseq_zero ncols)
     done
 lemma exchange_aux7:" foldseq_transposed op + (λk. foldseq_transposed op + (λka. Rep_matrix a k ka * Rep_matrix b ka k) n 
       + Rep_matrix a k (Suc n) * Rep_matrix b (Suc n) k) m =
       foldseq_transposed op + (λk. foldseq_transposed op + (λka. Rep_matrix a k ka * Rep_matrix b ka k) n ) m +
        foldseq_transposed op + (λk. Rep_matrix a k (Suc n) * Rep_matrix b (Suc n) k) m"
   apply(induct m,auto)
   done
lemma exchange_aux6:"foldseq_transposed op + (λk. foldseq_transposed op + (λka. Rep_matrix a k ka * Rep_matrix b ka k)  n ) m =
    foldseq_transposed op + (λk. foldseq_transposed op + (λka. Rep_matrix b k ka * Rep_matrix a ka k) m)  n"
    apply(induct n,auto)
    apply (simp add: mult.commute)
    apply(simp add:exchange_aux7)
   by (simp add: mult.commute)


lemma exchange_aux13:"
    foldseq_transposed op + (λk. Rep_matrix (mult_matrix_n (Matrix.Max (nrows a) (ncols a) (nrows b) (ncols b)) op * op + a b) k k)
     (Matrix.Max (nrows a) (ncols a) (nrows b) (ncols b)) =
    foldseq_transposed op + (λk. Rep_matrix (mult_matrix_n (Matrix.Max (nrows a) (ncols a) (nrows b) (ncols b)) op * op + b a) k k)
     (Matrix.Max (nrows a) (ncols a) (nrows b) (ncols b))"
apply(simp add:mult_matrix_n_def)
apply(simp add:exchange_aux4)
apply(simp add:exchange_aux5)
apply(subgoal_tac " (λk. foldseq op + (λka. Rep_matrix a k ka * Rep_matrix b ka k) (Matrix.Max (nrows a) (ncols a) (nrows b) (ncols b)))
     =
 (λk. foldseq_transposed op + (λka. Rep_matrix a k ka * Rep_matrix b ka k) (Matrix.Max (nrows a) (ncols a) (nrows b) (ncols b)))")
prefer 2
apply (simp add: associative_def foldseq_assoc)
apply(subgoal_tac " (λk. foldseq op + (λka. Rep_matrix b k ka * Rep_matrix a ka k) (Matrix.Max (nrows a) (ncols a) (nrows b) (ncols b))) =
   (λk. foldseq_transposed op + (λka. Rep_matrix b k ka * Rep_matrix a ka k) (Matrix.Max (nrows a) (ncols a) (nrows b) (ncols b)))")
prefer 2
apply (simp add: associative_def foldseq_assoc)
by (simp add: exchange_aux6)

lemma exchange_tr_aux15:" foldseq_transposed op + (λk. Rep_matrix (mult_matrix_n (Matrix.Max (nrows a) (ncols a) (nrows b) (ncols b)) op * op + a b) k k)
     (Matrix.Max (nrows a) (ncols a) (nrows b) (ncols b)) =
    foldseq_transposed op + (λk. Rep_matrix (mult_matrix_n (Matrix.Max (nrows a) (ncols a) (nrows b) (ncols b)) op * op + b a) k k)
     (Matrix.Max (nrows a) (ncols a) (nrows b) (ncols b)) ⟹
 foldseq_transposed op + (λk. Rep_matrix (mult_matrix_n (Matrix.Max (nrows a) (ncols a) (nrows b) (ncols b)) op * op + a b) k k)
     (Matrix.Max (nrows a) (ncols a) (nrows b) (ncols b)) =
    foldseq_transposed op + (λk. Rep_matrix (mult_matrix_n (Matrix.Max (nrows b) (ncols b) (nrows a) (ncols a)) op * op + b a) k k)
     (Matrix.Max (nrows b) (ncols b) (nrows a) (ncols a))"
     apply(subgoal_tac "(Matrix.Max (nrows b) (ncols b) (nrows a) (ncols a)) =
           (Matrix.Max (nrows a) (ncols a) (nrows b) (ncols b))")
     apply auto
     apply(simp add:Max_def)
by (simp add: max.commute max.left_commute)


(* Tr a*b= Tr b*a *)
lemma exchange_tr:"Tr (mat_mult a b) =Tr (mat_mult b a)"
apply(simp add:eql)
apply(simp add:trace_def)
apply(simp add: mat_mult_def)
apply(simp add:exchange_aux1 )
apply(simp add:times_matrix_def)
apply(simp add:mult_matrix_def)
apply(simp add:exchange_aux2)
apply(rule exchange_tr_aux15)
using exchange_aux13 by blast



lemma tr_pow_aux1:"foldseq_transposed op + (λk. Rep_matrix (mat_mult A (dag A)) k k) (max (nrows (mat_mult A (dag A))) (ncols (mat_mult A (dag A))))
=foldseq op + (λk. Rep_matrix (mat_mult A (dag A)) k k) (max (nrows (mat_mult A (dag A))) (ncols (mat_mult A (dag A))))"
apply (simp add: associative_def foldseq_assoc)
done
lemma tr_pow_aux2:"foldseq op + (λk. Rep_matrix (mat_mult A (dag A)) k k) (max (nrows (mat_mult A (dag A))) (ncols (mat_mult A (dag A))))
=foldseq op + (λk. Rep_matrix (mat_mult A (dag A)) k k) (max (nrows A) (ncols A))"
 apply(rule foldseq_zerotail,auto)
 apply (simp add: nrows)
 apply (simp add: max1 mult_nrow)
 by (metis dag_def max.commute max2 mult_ncol ncols_transpose)
lemma tr_pow_aux3:"Rep_matrix (dag A) k i =Rep_matrix A i k"
by (simp add: dag_def)
lemma tr_pow_aux4:" (max (ncols A) (nrows (dag A))) = ncols A"
by (simp add: dag_def)
lemma tr_pow_aux5:"Rep_matrix (Abs_matrix (λj i. foldseq op + (λk. Rep_matrix A j k * Rep_matrix A i k) (ncols A))) =
  (λj i. foldseq op + (λk. Rep_matrix A j k * Rep_matrix A i k) (ncols A))"
   apply(rule RepAbs_matrix)
   apply(rule_tac x=" nrows A" in exI)
   apply (simp add: foldseq_zero nrows)
   apply(rule_tac x=" nrows A" in exI)
   apply (simp add: foldseq_zero nrows)
   done
   (* Tr (A*A†) =∑(A i j)*(A i j) *)
lemma tr_pow:"Tr (mat_mult A (dag A)) =all_sum_pow A"
apply(simp add:eql)
apply(simp add:trace_def)
apply(simp add:tr_pow_aux1)
apply(simp add:tr_pow_aux2)
apply(simp add: mat_mult_def)
apply(simp add:times_matrix_def)
apply(simp add:mult_matrix_def)
apply(simp add:mult_matrix_n_def)
apply(simp add:tr_pow_aux3)
apply(simp add:tr_pow_aux4)
apply(simp add:tr_pow_aux5)
apply(simp add:all_sum_pow_def)
apply(simp add:rows_sum_pow_def)
by (simp add: foldseq_zero foldseq_zerotail max_def nrows)

type_synonym number=nat
type_synonym nT="nat⇒Mat"
primrec h::"nat⇒nat list"where
"h 0=[]"|
"h (Suc n) =(Suc n)# (h n)"
(*consts h::"nat⇒nat list"*)
(*    |0><n|  *)
consts f::"nat⇒Mat"
(*    |n><0|  *)
consts g::"nat⇒Mat"
(*positive matrix*)
definition positive::"Mat⇒bool" where
"positive A=(∃m. mat_mult m (dag m) =A)"
(*U matrix*)
definition UMat::"Mat⇒bool" where
"UMat a= (mat_mult (dag a) a=I) "
(*   a⊑b      *)
definition less::"Mat⇒Mat⇒bool" where
"less A B=positive (mat_sub B A)"
lemma aux2:" Rep_matrix (Abs_matrix (λj i. foldseq op + (λk. Rep_matrix B j k * Rep_matrix B i k)
         (max (ncols B) (nrows (Abs_matrix (transpose_infmatrix (Rep_matrix B))))))) =
       (λj i. foldseq op + (λk. Rep_matrix B j k * Rep_matrix B i k)
         (max (ncols B) (nrows (Abs_matrix (transpose_infmatrix (Rep_matrix B))))))  "
 apply(rule RepAbs_matrix)
 apply(rule_tac x=" (max (nrows B) (ncols B))" in exI)
 apply (simp add: foldseq_zero nrows)
 apply(rule_tac x=" (max (nrows B) (ncols B))" in exI)
 apply (simp add: foldseq_zero nrows)
 done
lemma aux5:" 0 ≤ foldseq_transposed op + (λka. Rep_matrix B m ka * Rep_matrix B m ka) n"
apply(induct n,auto)
done
lemma aux4:" 0 ≤ foldseq_transposed op +
          (λk. foldseq_transposed op + (λka. Rep_matrix B k ka * Rep_matrix B k ka)
                (max (ncols B) (nrows (Abs_matrix (transpose_infmatrix (Rep_matrix B))))))
          n"
  apply(induct n,auto)
  apply(simp add:aux5)+
  done
lemma aux3:" 0 ≤  foldseq_transposed  op + (λk. Rep_matrix (mat_mult B (dag B)) k k) n"
apply(simp add:dag_def transpose_matrix_def mat_mult_def times_matrix_def)
apply(simp add:mult_matrix_def mult_matrix_n_def)
apply(simp add:aux2)
apply(subgoal_tac " (λk. foldseq op + (λka. Rep_matrix B k ka * Rep_matrix B k ka)
                (max (ncols B) (nrows (Abs_matrix (transpose_infmatrix (Rep_matrix B)))))) =
                 (λk. foldseq_transposed op + (λka. Rep_matrix B k ka * Rep_matrix B k ka)
                (max (ncols B) (nrows (Abs_matrix (transpose_infmatrix (Rep_matrix B))))))")
prefer 2
apply (simp add: associative_def foldseq_assoc)
apply(simp add:aux4)
done
lemma aux1:"Tr (mat_mult B (dag B)) ≥0"
apply(simp add:eql)
apply(simp add:trace_def)
apply(simp add:aux3)
done
(*positive A⟹Tr A≥0*)
lemma positive_Tr1:"A=mat_mult B (dag B) ⟹Tr A≥0"
apply(subgoal_tac "Tr (mat_mult B (dag B)) ≥0")
apply auto
apply(simp add:aux1)
done
lemma positive_Tr:"positive A⟹Tr A≥0"
apply(simp add:positive_def)
using positive_Tr1 by auto
(*a≥0,b≥0⟹Tr(a*b)≥0 *)
lemma less44:"positive a⟹positive b⟹Tr (mat_mult a b) ≥0"
apply(simp add:positive_def,auto)
apply(subgoal_tac " Tr (mat_mult ( mat_mult  (mat_mult m (dag m)) ma)   (dag ma) )≥0 ")
apply (simp add: mult_exchange)
apply(subgoal_tac " 0 ≤ Tr (mat_mult   (dag ma)  (mat_mult (mat_mult m (dag m)) ma)) ")
apply (simp add: exchange_tr)
apply(subgoal_tac " 0 ≤ Tr (mat_mult (mat_mult (dag ma) m)  (mat_mult (dag m) ma)  )  ")
apply (simp add: mult_exchange)
apply(subgoal_tac " 0 ≤ Tr (mat_mult (mat_mult (dag ma) m)  (dag (mat_mult (dag ma) m))) ")
apply (simp add: dag_dag dag_mult)
apply (simp add: positive_Tr1)
done
(*   a obvious lemma. There are three equivalent definiton of positive matrix *)
axiomatization where positive_definition : "A=dag A⟹ ∀v. Rep_matrix (mat_mult (mat_mult v A) (dag v)) 0 0≥0⟹positive A"


lemma posi_decide:"A=dag A⟹∀v. Rep_matrix (mat_mult (mat_mult v A) (dag v)) 0 0≥0⟹positive A"
apply(simp add: positive_definition)
done
lemma posi_aux1:"∀v. 0 ≤ Rep_matrix (mat_mult v  (dag v)) 0 0"
apply auto
apply(simp add:mat_mult_def)
apply(simp add:times_matrix_def)
apply(simp add:mult_matrix_def)
apply(simp add:mult_matrix_n_def)
apply(subgoal_tac " Rep_matrix (Abs_matrix (λj i. foldseq op + (λk. Rep_matrix v j k * Rep_matrix (dag v) k i) (max (ncols v) (nrows (dag v))))) =
   (λj i. foldseq op + (λk. Rep_matrix v j k * Rep_matrix (dag v) k i) (max (ncols v) (nrows (dag v))))")
prefer 2
 apply(rule RepAbs_matrix)
 apply(rule_tac x=" (max (nrows v) (nrows (dag v)))" in exI)
  apply (simp add: foldseq_zero nrows)
  apply(rule_tac x=" ncols (dag v)" in exI)
  apply (simp add: foldseq_zero ncols)
  apply auto
  apply(subgoal_tac " foldseq op + (λk. Rep_matrix v 0 k * Rep_matrix (dag v) k 0) (max (ncols v) (nrows (dag v))) =
        foldseq op + (λk. Rep_matrix v 0 k * Rep_matrix  v 0 k) (max (ncols v) (nrows (dag v))) ")
  prefer 2
 using tr_pow_aux3 apply auto
 apply(subgoal_tac "0 ≤ foldseq_transposed op + (λk. Rep_matrix v 0 k * Rep_matrix v 0 k) (max (ncols v) (nrows (dag v))) ")
apply (simp add: associative_def foldseq_assoc)
by (simp add: aux5)
lemma posi1:" positive A⟹∀v. Rep_matrix (mat_mult (mat_mult v A) (dag v)) 0 0≥0"
apply(simp add:positive_def)
apply(erule exE,auto)
apply(subgoal_tac " 0 ≤ Rep_matrix (mat_mult (mat_mult v  m ) (mat_mult (dag m) (dag v))) 0 0 ")
apply (simp add: mult_exchange)
by (metis dag_mult posi_aux1)
lemma less6_aux_aux:" Rep_matrix (mat_add a b) 0 0 =
             Rep_matrix a 0 0 + Rep_matrix b 0 0"
         apply(simp add:mat_add_def matplus_def)
         done
lemma less6_aux:"∀a.∀b. positive a⟶positive b⟶positive (mat_add a b)"
apply auto
apply(rule posi_decide,auto)
prefer 2
apply(subgoal_tac " Rep_matrix (mat_mult (mat_mult v (mat_add a b)) (dag v)) 0 0= Rep_matrix (mat_mult (mat_mult v  a) (dag v)) 0 0+ Rep_matrix (mat_mult (mat_mult v  b) (dag v)) 0 0 ")
prefer 2
apply(subgoal_tac "mat_mult (mat_mult v (mat_add a b)) (dag v) =
     mat_add (mat_mult (mat_mult v  a) (dag v)) (mat_mult (mat_mult v  b) (dag v)) ")
prefer 2
apply(subgoal_tac " mat_mult (mat_mult v (mat_add a b)) (dag v) =  mat_mult(  mat_add (mat_mult v a )  (mat_mult v b) ) (dag v)")
prefer 2
apply (simp add: mult_allo2,auto)
apply (simp add: mult_allo1)
apply (simp add: less6_aux_aux)
apply(subgoal_tac "∀v. Rep_matrix (mat_mult (mat_mult v a) (dag v)) 0 0≥0")
apply(subgoal_tac "∀v. Rep_matrix (mat_mult (mat_mult v b) (dag v)) 0 0≥0")
prefer 2
using posi1 apply blast
prefer 2
using posi1 apply blast
apply(drule_tac x="v"in spec)+
apply auto
apply(subgoal_tac "a=dag a")
prefer 2
using Matrix.positive_def dag_dag dag_mult apply auto[1]
apply(subgoal_tac "b=dag b")
prefer 2
using Matrix.positive_def dag_dag dag_mult apply auto[1]
by (simp add: dag_def transpose_matrix_add)
lemma less6:"∀a.∀b.∀c.∀d. less a b⟶less c d⟶less (mat_add a c) (mat_add b d)"
apply(simp add:less_def)
apply(auto)
apply(subgoal_tac "positive (mat_add (mat_sub b a) (mat_sub d c) )")
apply(subgoal_tac "(mat_add (mat_sub b a) (mat_sub d c)) =(mat_sub (mat_add b d) (mat_add a c))")
apply simp
apply (metis a b l ll mat_add_def mat_sub_def)
apply(simp add:less6_aux)
done

(*a>0 b>0⟹Tr (ab)≥0*)
lemma less4:"∀a.∀b. less zero a⟶less zero b⟶Tr (mat_mult a b) ≥0"
apply (simp add: less44 less_def zero_sub)
done
(* Tr a*b= Tr b*a *)
lemma exchange:"Tr (mat_mult a b) =Tr (mat_mult b a)"
apply (simp add:exchange_tr)
done
lemma I_zero:"less zero I"
apply(simp add:less_def)
apply(subgoal_tac "positive I")
apply (simp add:zero_sub)
apply(simp add:positive_def)
by (metis Ident dag_I)
(*a≥a*)
lemma less11:" less a a"
apply(simp add:less_def)
apply(subgoal_tac "positive zero ")
apply (simp add: sub_self)
using positive_def zero_mult_l by auto
(*dag U * U=I*)
lemma U_dag:"UMat a ⟶ mat_mult (dag a) a=I"
apply(simp add:UMat_def)
done
lemma rho_zero:"∀ a. positive a ⟶ less zero  a"
apply (metis gg k l less_def mat_mult_def mat_sub_def zero_mult_r)
done
lemma a1:"∀a. less zero a⟶positive a"
apply (metis g gg l less_def m mat_sub_def)
done
(* less a b ⇒ less (a+c) (b+c)*)
lemma less10:"∀a.∀b. less a b⟶less (mat_add c a) (mat_add c b )"
by (simp add: less11 less6)
lemma less5:"∀a.∀b. less a b⟶less (mat_sub a c) (mat_sub b c)" 
by (metis Matrix.a l less10 mat_add_def mat_sub_def)
lemma less2: "less a b⟹(∀ c. positive c ⟶ Tr (mat_mult a c) ≤Tr (mat_mult b c))"
apply(subgoal_tac "less zero (mat_sub b a)")
using less4 mult_sub_allo1 rho_zero tr_allo1 apply fastforce
by (metis less5 sub_self)
lemma rho_tr:"∀ c. positive c ⟶  0 <=Tr c"
using I_zero Ident less2 zero_mult_l zero_tr by force
(*a>0 b>0⟹a+b>0*)
lemma c1:"positive a⟹positive b⟹positive (mat_add a b)"
by (metis a1 less6 rho_zero zero_add)
(*a<b b<c⟹>a<c*)
lemma  transitivity:"less a b⟹less b c⟹less a c"
apply(simp add:less_def)
apply(subgoal_tac "positive (mat_add (mat_sub b a) (mat_sub c b))")
prefer 2
apply(simp add:c1)
apply(subgoal_tac "positive (mat_add  (mat_sub c b) (mat_sub b a))")
prefer 2
apply (simp add: a mat_add_def)
apply(subgoal_tac "positive (mat_add (mat_add c (minus_matrix b)) (mat_add b (minus_matrix a)))")
prefer 2
apply (simp add: sub_add)
apply(simp add:mat_add_def)
apply(simp add:b)
apply(subgoal_tac "positive (matplus c   (matplus  (matplus (minus_matrix b)  b) (minus_matrix a)))")
prefer 2
apply(simp add:b)
by (metis a g l m mat_sub_def)
lemma less1:"less a b⟹less (mat_add c a) (mat_add c b )"
apply (simp add:less10)
done
lemma less3_aux:"positive A⟹positive (mat_mult (mat_mult B A) (dag B)) "
apply(simp add:positive_def)
by (metis dag_mult mult_exchange)
(* a≥0⟹m*a*m.T≥0  *)
lemma less3:" less zero  a⟹less zero (mat_mult (mat_mult b a) (dag b))"
apply(subgoal_tac "positive (mat_mult (mat_mult b a) (dag b))")
apply(simp add:rho_zero)
apply(subgoal_tac "positive a")
apply(simp add:less3_aux)
apply(simp add:a1)
done
lemma less_tr:"less A B⟹Tr A ≤Tr B"
apply(simp add:less_def)
apply(subgoal_tac "Tr (mat_sub B A)≥0")
apply (simp add: tr_allo1)
using positive_Tr by blast
lemma posi_aux:"∀v. 0 ≤ Rep_matrix (mat_mult v  (dag v)) 0 0"
apply auto
apply(simp add:mat_mult_def)
apply(simp add:times_matrix_def)
apply(simp add:mult_matrix_def)
apply(simp add:mult_matrix_n_def)
apply(subgoal_tac " Rep_matrix (Abs_matrix (λj i. foldseq op + (λk. Rep_matrix v j k * Rep_matrix (dag v) k i) (max (ncols v) (nrows (dag v))))) =
   (λj i. foldseq op + (λk. Rep_matrix v j k * Rep_matrix (dag v) k i) (max (ncols v) (nrows (dag v))))")
prefer 2
 apply(rule RepAbs_matrix)
 apply(rule_tac x=" (max (nrows v) (nrows (dag v)))" in exI)
  apply (simp add: foldseq_zero nrows)
  apply(rule_tac x=" ncols (dag v)" in exI)
  apply (simp add: foldseq_zero ncols)
  apply auto
  apply(subgoal_tac " foldseq op + (λk. Rep_matrix v 0 k * Rep_matrix (dag v) k 0) (max (ncols v) (nrows (dag v))) =
        foldseq op + (λk. Rep_matrix v 0 k * Rep_matrix  v 0 k) (max (ncols v) (nrows (dag v))) ")
  prefer 2
 using tr_pow_aux3 apply auto
 apply(subgoal_tac "0 ≤ foldseq_transposed op + (λk. Rep_matrix v 0 k * Rep_matrix v 0 k) (max (ncols v) (nrows (dag v))) ")
apply (simp add: associative_def foldseq_assoc)
by (simp add: aux5)
lemma posi:" positive A⟹∀v. Rep_matrix (mat_mult (mat_mult v A) (dag v)) 0 0≥0"
apply(simp add:positive_def)
apply(erule exE,auto)
apply(subgoal_tac " 0 ≤ Rep_matrix (mat_mult (mat_mult v  m ) (mat_mult (dag m) (dag v))) 0 0 ")
apply (simp add: mult_exchange)
by (metis dag_mult posi_aux)

lemma eq:"positive A≡(A=dag A) ∧ (∀v. Rep_matrix (mat_mult (mat_mult v A) (dag v)) 0 0≥0)"
by (smt Matrix.positive_def dag_dag dag_mult posi1 positive_definition)

lemma less20:"less a b⟹less (mat_mult (mat_mult (dag c) a) c) (mat_mult (mat_mult (dag c) b) c)"
apply(simp add:less_def)
by (metis dag_dag less3_aux mult_sub_allo1 mult_sub_allo2)

definition rows_sum_pow1::"matrix⇒nat⇒real"where
"rows_sum_pow1 A i=foldseq_transposed (op +) (%k. Rep_matrix A i k*Rep_matrix A i k) infinite"
definition all_sum_pow1::"matrix⇒real"where
"all_sum_pow1 A =foldseq_transposed (op +) (%k. rows_sum_pow1 A k) infinite"
definition rows_sum::"matrix⇒nat⇒real"where
"rows_sum A i=foldseq_transposed (op +) (%k. Rep_matrix A i k) infinite"
definition all_sum::"matrix⇒real"where
"all_sum A =foldseq_transposed (op +) (%k. rows_sum A k) infinite"
lemma all_sum_eq_aux1:" foldseq op + (λk. foldseq op + (λka. Rep_matrix A k ka * Rep_matrix A k ka) (ncols A)) (nrows A) =
       foldseq op + (λk. foldseq op + (λka. Rep_matrix A k ka * Rep_matrix A k ka) (ncols A)) infinite"
       apply(rule foldseq_zerotail,auto)
        apply (simp add: nrows)
        apply (simp add: foldseq_zero)
        done
lemma all_sum_eq_aux3:" foldseq op + (λka. Rep_matrix A k ka * Rep_matrix A k ka) (ncols A) =
               foldseq op + (λka. Rep_matrix A k ka * Rep_matrix A k ka) infinite"
                 apply(rule foldseq_zerotail,auto)
        apply (simp add: ncols)
        done
lemma all_sum_eq_aux2:"(λk. (foldseq_transposed op + (λka. Rep_matrix A k ka * Rep_matrix A k ka) infinite) ) =
            ( λk. (foldseq op + (λka. Rep_matrix A k ka * Rep_matrix A k ka) (ncols A)) )   "
      apply (rule ext)
      apply(simp add:all_sum_eq_aux3)
      by (simp add: associative_def foldseq_assoc)
lemma all_sum_eq:"all_sum_pow1 A=all_sum_pow A"
apply(simp add:all_sum_pow_def all_sum_pow1_def )
apply(simp add:rows_sum_pow_def)
apply(simp add:rows_sum_pow1_def)
apply(simp add:all_sum_eq_aux1)
apply(simp add:all_sum_eq_aux2)
by (simp add: associative_def foldseq_assoc)
lemma tr_pow1:"Tr (mat_mult A (dag A)) =all_sum_pow1 A"
apply(simp add:tr_pow all_sum_eq)
done

lemma Cua_Sch_aux:"((a::real)+(b::real))*((c::real)+(d::real)) =a*c+a*d+b*c+b*d"
apply(subgoal_tac "(a+b)*(c+d) =(a+b)*c+(a+b)*d")
prefer 2
apply (metis distrib_right mult.commute)
by (simp add: distrib_right)
lemma Cau_Sch_aux2:"foldseq_transposed op + (λk. (ff::nat⇒real) k * ff k) n ≥0"
apply(induct n,auto)
done
lemma Cau_Sch_aux1:" foldseq_transposed op + (λk. (ff::nat⇒real) k * ff k) n =
         sqrt (foldseq_transposed op + (λk. ff k * ff k) n) *sqrt (foldseq_transposed op + (λk. ff k * ff k) n) "
        apply auto
       by (simp add: Cau_Sch_aux2)
lemma Cau_Sch_aux3:" foldseq_transposed op + (λk. (ff::nat⇒real) k * ff k) n * ((gg::nat⇒real) (Suc n) * gg (Suc n)) =
           (sqrt (foldseq_transposed op + (λk. ff k * ff k) n) *gg (Suc n) ) *
            (sqrt (foldseq_transposed op + (λk. ff k * ff k) n) *gg (Suc n) )"
apply(subgoal_tac " foldseq_transposed op + (λk. (ff::nat⇒real) k * ff k) n * ((gg::nat⇒real) (Suc n) * gg (Suc n)) =
           sqrt (foldseq_transposed op + (λk. ff k * ff k) n)*sqrt (foldseq_transposed op + (λk. ff k * ff k) n)*
           ((gg::nat⇒real) (Suc n) * gg (Suc n))")
prefer 2
using Cau_Sch_aux1 apply auto[1]
apply auto
done
lemma Cau_Sch_aux4:" (ff::nat⇒real) (Suc n) * ff (Suc n) * foldseq_transposed op + (λk. (gg::nat⇒real) k * gg k) n =
                    (ff (Suc n)*(sqrt (foldseq_transposed op + (λk. gg k * gg k) n ))) *
                    (ff (Suc n)*(sqrt (foldseq_transposed op + (λk. gg k * gg k) n )))"
apply(subgoal_tac " ff (Suc n) * ff (Suc n) * foldseq_transposed op + (λk. gg k * gg k) n =
                   ff (Suc n) * ff (Suc n) * sqrt (foldseq_transposed op + (λk. gg k * gg k) n)
                                           * sqrt (foldseq_transposed op + (λk. gg k * gg k) n)")
prefer 2
using Cau_Sch_aux1 apply auto[1]
apply auto
done
lemma Cau_Sch_aux5:"(a::real)*a+(b::real)*b≥ 2* a* b"
by (smt power2_eq_square sum_squares_bound)

lemma Cau_Sch_aux55:"(a::real)*a+(b::real)*b≥ 2* abs(a)* abs(b)"
by (metis Cau_Sch_aux5 abs_mult_self)

lemma Cau_Sch_aux6:"foldseq_transposed op + (λk. (ff::nat⇒real) k * ff k) n * ((gg::nat⇒real) (Suc n) * gg (Suc n)) +
            ff (Suc n) * ff (Suc n) * foldseq_transposed op + (λk. gg k * gg k) n ≥
            2*abs (sqrt (foldseq_transposed op + (λk. ff k * ff k) n) *gg (Suc n) )*
           abs (ff (Suc n)*(sqrt (foldseq_transposed op + (λk. gg k * gg k) n )))"
apply(simp add:Cau_Sch_aux3 Cau_Sch_aux4 )
apply(simp add:Cau_Sch_aux55)
done
lemma Cau_Sch_aux9:"abs(a::real)*abs(b::real)≤(c::real)⟹a*b≤c"
by (metis abs_le_D1 abs_mult)
lemma Cau_Sch_aux11:"abs(a::real)≤abs(b::real)*abs(e::real) ⟹abs(c)*abs(d)*abs(a) ≤abs(c)*abs(d)*(abs(b)*abs(e))"
by (simp add: mult_left_mono)
lemma Cau_Sch_aux10:"abs(a::real)≤abs(b::real)*abs(e::real) ⟹abs(c)*abs(d)*abs(a) ≤abs(c)*abs(d)*abs(b)*abs(e)"
by (metis Cau_Sch_aux11 mult.assoc)
lemma Cau_Sch_aux12:"sqrt(a*b) =sqrt(a::real)*sqrt(b::real)"
by (simp add: real_sqrt_mult_distrib2)
lemma Cau_Sch_aux7:" foldseq_transposed op + (λk. (ff::nat⇒real) k * (gg::nat⇒real) k) n * foldseq_transposed op + (λk. ff k * gg k) n
         ≤ foldseq_transposed op + (λk. ff k * ff k) n * foldseq_transposed op + (λk. gg k * gg k) n ⟹
         2 * (ff (Suc n) * (gg (Suc n) * foldseq_transposed op + (λk. ff k * gg k) n))
         ≤ 2 * abs(sqrt (foldseq_transposed op + (λk. ff k * ff k) n) * gg (Suc n)) *
            abs (ff (Suc n) * sqrt (foldseq_transposed op + (λk. gg k * gg k) n))"
         apply auto

         apply(subgoal_tac " abs (foldseq_transposed op + (λk. ff k * gg k) n )
             ≤  sqrt (foldseq_transposed op + (λk. ff k * ff k) n * foldseq_transposed op + (λk. gg k * gg k) n)")
         prefer 2
         apply (simp add: power2_eq_square real_le_rsqrt)
         apply(rule Cau_Sch_aux9)
         apply(simp add:abs_mult)
         apply(subgoal_tac " ¦ff (Suc n)¦ * (¦gg (Suc n)¦ * ¦foldseq_transposed op + (λk. ff k * gg k) n¦)
                   ≤ (¦ff (Suc n)¦ *¦gg (Suc n)¦ * ¦sqrt (foldseq_transposed op + (λk. ff k * ff k) n)¦ * 
                      ¦sqrt (foldseq_transposed op + (λk. gg k * gg k) n)¦)")
         apply (simp add: mult.assoc mult.left_commute)
         apply(cut_tac a="foldseq_transposed op + (λk. ff k * gg k) n" and b="sqrt (foldseq_transposed op + (λk. ff k * ff k) n)"
              and c="ff (Suc n)" and  d="gg (Suc n)" and e="sqrt (foldseq_transposed op + (λk. gg k * gg k) n)"in Cau_Sch_aux10)
         prefer 2
         apply auto
         apply(subgoal_tac "sqrt (foldseq_transposed op + (λk. ff k * ff k) n * foldseq_transposed op + (λk. gg k * gg k) n) =
           sqrt (foldseq_transposed op + (λk. ff k * ff k) n )*sqrt( foldseq_transposed op + (λk. gg k * gg k) n)")
         prefer 2
        using Cau_Sch_aux12 apply blast
        apply auto
        by (metis (no_types) abs_ge_self abs_mult order_trans)
lemma Cau_Sch_aux8:"(a::real)≤b⟹b≤c⟹a≤c"
apply auto
done
(* Cauchy Schwartz  inequality  *)
lemma Cau_Sch:"(foldseq_transposed (op +) (%k. ((ff::nat⇒real) k)*((gg::nat⇒real) k) ) n) *
               (foldseq_transposed (op +) (%k. ((ff::nat⇒real) k)*((gg::nat⇒real) k) ) n) ≤
               (foldseq_transposed (op +) (%k. (ff k)*(ff k) ) n)*
               (foldseq_transposed (op +) (%k. (gg k)*(gg k) ) n)"
    apply(induct n,auto)
    apply(simp add:Cua_Sch_aux)
    apply(subgoal_tac " 2 * (ff (Suc n) * (gg (Suc n) * foldseq_transposed op + (λk. ff k * gg k) n))
            ≤ (foldseq_transposed op + (λk. ff k * ff k) n * (gg (Suc n) * gg (Suc n)) +
             ff (Suc n) * ff (Suc n) * foldseq_transposed op + (λk. gg k * gg k) n)")
    apply auto
   apply(cut_tac a="2 * (ff (Suc n) * (gg (Suc n) * foldseq_transposed op + (λk. ff k * gg k) n))"and
              b="2*abs (sqrt (foldseq_transposed op + (λk. ff k * ff k) n) *gg (Suc n) )*
                 abs (ff (Suc n)*(sqrt (foldseq_transposed op + (λk. gg k * gg k) n )))" and 
              c="foldseq_transposed op + (λk. ff k * ff k) n * (gg (Suc n) * gg (Suc n)) +
               ff (Suc n) * ff (Suc n) * foldseq_transposed op + (λk. gg k * gg k) n "in Cau_Sch_aux8)
   apply(simp add:Cau_Sch_aux7)
   apply(simp add:Cau_Sch_aux6)
   apply auto
   done
 lemma advance_aux2:"a*(foldseq_transposed (op+) (ff::nat⇒real) n ) =foldseq_transposed (op+) (%i. a*(ff i) ) n"
 apply(induct n,auto)
by (simp add: distrib_left)
(* (∑ai)^2=∑∑ai*aj  *)
 lemma advance_aux1:"(foldseq_transposed (op+) (ff::nat⇒real) n)*(foldseq_transposed (op+) (ff::nat⇒real) m)
               =foldseq_transposed (op+) (%i. foldseq_transposed (op+) (%j. ff i * ff j) m   ) n " 
   apply(induct n,auto)
   apply(simp add:advance_aux2)
by (simp add: advance_aux2 distrib_left mult.commute)
lemma advance_aux3:"foldseq_transposed op + (λk. foldseq_transposed op + (λka. Rep_matrix m k ka * Rep_matrix m k ka) infinite) infinite *
   foldseq_transposed op + (λk. foldseq_transposed op + (λka. Rep_matrix m k ka * Rep_matrix m k ka) infinite) infinite =
       foldseq_transposed (op+) (%i. foldseq_transposed (op+) (%j.  (λk. foldseq_transposed op + (λka. Rep_matrix m k ka *
     Rep_matrix m k ka)  infinite) i *
         (λk. foldseq_transposed op + (λka. Rep_matrix m k ka * Rep_matrix m k ka) infinite) j) infinite   ) infinite"
          apply (simp add:advance_aux1)
          done
lemma advance_aux5:"foldseq_transposed op + (λk. foldseq_transposed op + (λka. Rep_matrix m k ka * Rep_matrix m k ka) infinite) infinite *
   foldseq_transposed op + (λk. foldseq_transposed op + (λka. Rep_matrix m k ka * Rep_matrix m k ka) infinite) infinite =
    foldseq_transposed (op+) (%i. foldseq_transposed (op+) (%j.  
           (foldseq_transposed op +(λka. Rep_matrix m i ka * Rep_matrix m i ka) infinite)  *
           (foldseq_transposed op + (λka. Rep_matrix m j ka * Rep_matrix m j ka) infinite) 
          )  infinite) infinite"
by (simp add: advance_aux1)
lemma advance_aux6:"  foldseq_transposed op + (λka. Rep_matrix m i ka * Rep_matrix m i ka) infinite *
                   foldseq_transposed op + (λka. Rep_matrix m j ka * Rep_matrix m j ka) infinite ≥
                     foldseq_transposed op + (λka. Rep_matrix m i ka * Rep_matrix m j ka) infinite *
                     foldseq_transposed op + (λka. Rep_matrix m i ka * Rep_matrix m j ka) infinite"
using Cau_Sch by blast
lemma advance_aux8:"∀i.(ff::nat⇒real) i≤(gg::nat⇒real) i⟹foldseq_transposed (op+) ff n≤foldseq_transposed (op+) gg n"
apply(induct n,auto)
by (simp add: add_mono)
lemma advance_aux7:" foldseq_transposed op +
        (λi. foldseq_transposed op +
              (λj. foldseq_transposed op + (λka. Rep_matrix m i ka * Rep_matrix m i ka) infinite *
                   foldseq_transposed op + (λka. Rep_matrix m j ka * Rep_matrix m j ka) infinite)
              infinite)
        infinite ≥
         foldseq_transposed op +
        (λi. foldseq_transposed op +
              (λj. foldseq_transposed op + (λka. Rep_matrix m i ka * Rep_matrix m j ka) infinite *
                     foldseq_transposed op + (λka. Rep_matrix m i ka * Rep_matrix m j ka) infinite)
              infinite)
        infinite"
apply(rule advance_aux8,auto)
apply(rule advance_aux8,auto)
by (simp add: Cau_Sch)
lemma advance_aux9:"a≤b⟹b≤c⟹(a::real)≤c"
by simp
lemma advance_aux11:"∀i.(ff::nat⇒real) i=(gg::nat⇒real) i⟹foldseq_transposed (op+) ff n=foldseq_transposed (op+) gg n"
apply(induct n,auto)
done
lemma advance_aux10:" foldseq_transposed op +
     (λk. foldseq_transposed op +
           (λka. Rep_matrix
                  (Abs_matrix (λj i. foldseq op + (λk. Rep_matrix m j k * Rep_matrix (dag m) k i) (max (ncols m) (nrows (dag m))))) k ka *
                 Rep_matrix
                  (Abs_matrix (λj i. foldseq op + (λk. Rep_matrix m j k * Rep_matrix (dag m) k i) (max (ncols m) (nrows (dag m))))) k ka)
           infinite)
     infinite= foldseq_transposed op +
     (λk. foldseq_transposed op +
           (λka. Rep_matrix
                  (Abs_matrix (λj i. foldseq op + (λk. Rep_matrix m j k * Rep_matrix (dag m) k i) infinite )) k ka *
                 Rep_matrix
                  (Abs_matrix (λj i. foldseq op + (λk. Rep_matrix m j k * Rep_matrix (dag m) k i) infinite )) k ka)
           infinite)
     infinite"
     apply(rule advance_aux11,auto)
      apply(rule advance_aux11,auto)
      apply(subgoal_tac "Rep_matrix (Abs_matrix (λj i. foldseq op + (λk. Rep_matrix m j k * Rep_matrix (dag m) k i) infinite)) i ia=
       Rep_matrix (Abs_matrix (λj i. foldseq op + (λk. Rep_matrix m j k * Rep_matrix (dag m) k i) (max (ncols m) (nrows (dag m))))) i
             ia ")
      apply auto
      apply(subgoal_tac "(Abs_matrix (λj i. foldseq op + (λk. Rep_matrix m j k * Rep_matrix (dag m) k i) infinite)) =
        (Abs_matrix (λj i. foldseq op + (λk. Rep_matrix m j k * Rep_matrix (dag m) k i) (max (ncols m) (nrows (dag m)))))")
      apply auto
      apply(subgoal_tac "(λj i. foldseq op + (λk. Rep_matrix m j k * Rep_matrix (dag m) k i) infinite) =
        (λj i. foldseq op + (λk. Rep_matrix m j k * Rep_matrix (dag m) k i) (max (ncols m) (nrows (dag m)))) ")
      apply auto
      apply (rule ext)+
      apply(cut_tac f="op+" and s="(λk. (Rep_matrix m j k * Rep_matrix (dag m) k i) )" and 
                m="infinite" and n="(max (ncols m) (nrows (dag m)))" in foldseq_zerotail)
      apply auto
using ncols by blast
 lemma advance_aux:" Tr (mat_mult (mat_mult m (dag m)) (dag (mat_mult m (dag m)))) ≤
         Tr (mat_mult m (dag m)) * Tr (mat_mult m (dag m))"
         apply(simp add:tr_pow1)   
         apply(simp add:all_sum_pow1_def rows_sum_pow1_def)
         apply(subgoal_tac " foldseq_transposed op +
     (λk. foldseq_transposed op + (λka. Rep_matrix (mat_mult m (dag m)) k ka * Rep_matrix (mat_mult m (dag m)) k ka) infinite) infinite
    ≤ foldseq_transposed (op+) (%i. foldseq_transposed (op+) (%j.  
           (foldseq_transposed op +(λka. Rep_matrix m i ka * Rep_matrix m i ka) infinite)  *
           (foldseq_transposed op + (λka. Rep_matrix m j ka * Rep_matrix m j ka) infinite) 
          )  infinite) infinite ")
apply (simp add: advance_aux1)
apply(subgoal_tac " foldseq_transposed op +
     (λk. foldseq_transposed op + (λka. Rep_matrix (mat_mult m (dag m)) k ka * Rep_matrix (mat_mult m (dag m)) k ka) infinite) infinite
    ≤  foldseq_transposed op +
        (λi. foldseq_transposed op +
              (λj. foldseq_transposed op + (λka. Rep_matrix m i ka * Rep_matrix m j ka) infinite *
                     foldseq_transposed op + (λka. Rep_matrix m i ka * Rep_matrix m j ka) infinite)
              infinite)
        infinite")
   apply(cut_tac a=" foldseq_transposed op +
     (λk. foldseq_transposed op + (λka. Rep_matrix (mat_mult m (dag m)) k ka * Rep_matrix (mat_mult m (dag m)) k ka) infinite) infinite"
      and b="foldseq_transposed op +
        (λi. foldseq_transposed op +
              (λj. foldseq_transposed op + (λka. Rep_matrix m i ka * Rep_matrix m j ka) infinite *
                   foldseq_transposed op + (λka. Rep_matrix m i ka * Rep_matrix m j ka) infinite)
              infinite)
        infinite" and c=" foldseq_transposed op +
        (λi. foldseq_transposed op +
              (λj. foldseq_transposed op + (λka. Rep_matrix m i ka * Rep_matrix m i ka) infinite *
                   foldseq_transposed op + (λka. Rep_matrix m j ka * Rep_matrix m j ka) infinite)
              infinite)
        infinite" in advance_aux9)
   apply auto
apply (simp add: advance_aux7)
apply(simp add:mat_mult_def )
apply(simp add:times_matrix_def)
apply(simp add:mult_matrix_def)
apply(simp add:mult_matrix_n_def)
apply(subgoal_tac "foldseq_transposed op +
     (λk. foldseq_transposed op +
           (λka. Rep_matrix
                  (Abs_matrix (λj i. foldseq op + (λk. Rep_matrix m j k * Rep_matrix (dag m) k i) infinite )) k ka *
                 Rep_matrix
                  (Abs_matrix (λj i. foldseq op + (λk. Rep_matrix m j k * Rep_matrix (dag m) k i) infinite )) k ka)
           infinite)
     infinite ≤ foldseq_transposed op +
        (λi. foldseq_transposed op +
              (λj. foldseq_transposed op + (λka. Rep_matrix m i ka * Rep_matrix m j ka) infinite *
                   foldseq_transposed op + (λka. Rep_matrix m i ka * Rep_matrix m j ka) infinite)
              infinite)
        infinite ")
apply (simp add: advance_aux10)
apply(rule advance_aux8,auto)
apply(rule advance_aux8,auto)
apply(subgoal_tac "Rep_matrix (Abs_matrix (λj i. foldseq op + (λk. Rep_matrix m j k * Rep_matrix (dag m) k i) infinite))  =
     (λj i. foldseq op + (λk. Rep_matrix m j k * Rep_matrix (dag m) k i) infinite)",auto)
prefer 2
apply(rule RepAbs_matrix)
 apply(rule_tac x="infinite" in exI)
  apply (simp add: foldseq_zero ,auto)
apply (metis (no_types, lifting) add.left_neutral foldseq_zero mult_zero_left ncols_max ncols_transpose nrows_le)
 apply(rule_tac x="infinite" in exI)     
apply (simp add: foldseq_zero,auto)
apply (metis (no_types, lifting) add.right_neutral foldseq_zero mult.commute mult_zero_left ncols_max ncols_transpose nrows_le tr_pow_aux3)
 apply(subgoal_tac " foldseq op + (λk. Rep_matrix m i k * Rep_matrix (dag m) k ia) infinite =
      foldseq_transposed op + (λka. Rep_matrix m i ka * Rep_matrix m ia ka) infinite")
 apply auto
 apply(subgoal_tac "foldseq op + (λk. Rep_matrix m i k * Rep_matrix (dag m) k ia) infinite =
   foldseq_transposed op + (λk. Rep_matrix m i k * Rep_matrix (dag m) k ia) infinite",auto)
 prefer 2
apply (simp add: associative_def foldseq_assoc)
apply(rule advance_aux11,auto)
by (simp add: tr_pow_aux3)
   (* a≥0⟹Tr (a*a.T)≤(Tr a)^2 *)
 lemma advance:"positive A⟹Tr (mat_mult A (dag A))≤ (Tr A)*(Tr A)"
 apply(simp add:positive_def,auto)
 apply(simp add:advance_aux)
 done
end
