theory quantum_hoare_logic
imports Main  Matrix Limits convergent
begin




(*The datatype for representing syntax of quantum programs*)
datatype
com=SKIP
|Init "nat" "number"
|Utrans "Mat" "number"
|Seq "com" "com"          ("(_;/ _)"   [61,59] 60  )
|Cond "(Mat * com * Mat) list"  
|While "Mat" "Mat" "com" "Mat" 


primrec M_sum::"(Mat*com*Mat) list⇒Mat"where
"M_sum [] =zero"|
"M_sum (a#M) =mat_add (mat_mult (dag (fst a) ) (fst a)) (M_sum M )"
primrec sum::"nat list⇒nT⇒Mat⇒Mat" where
"sum [] f1 p=p"|
"sum (b#nl) f1 p = mat_add (mat_mult (mat_mult (f1 b) p) (dag (f1 b)) ) (sum nl f1 p )"
primrec sum_t::"nat list⇒nT⇒Mat⇒Mat"where
"sum_t [] f1 p=p"|
"sum_t (b#nl) f1 p = mat_add (mat_mult (mat_mult (dag (f1 b)) p)  (f1 b) ) (sum_t nl f1 p )"
primrec sum_1::"nat list⇒nT⇒Mat" where
"sum_1 [] f1 =I"|
"sum_1 (b#nl) f1 =mat_add (mat_mult (f1 b) (dag (f1 b))) (sum_1 nl f1)"
primrec sum_2::"nat list⇒nT⇒Mat" where
"sum_2 [] f1 =I"|
"sum_2 (b#nl) f1 =mat_add (mat_mult (dag (f1 b))  (f1 b)   ) (sum_2 nl f1)"
(*u a b =ab(dag a) *)
definition u::"Mat⇒Mat⇒Mat"where
"u a b= mat_mult (mat_mult a b) (dag a)"
(*uu a b =(dag a)ba *)
definition uu::"Mat⇒Mat⇒Mat"where
"uu a b= mat_mult (mat_mult (dag a) b)  a"
primrec accum::"(Mat*com*Mat) list⇒Mat" where
"accum [] =zero"|
"accum (a#M) = mat_add (snd (snd a)) (accum M)"
 (*the rank function that defined for the denoFun*)
fun rank :: "com⇒nat" where
"rank SKIP =1"|
"rank (Utrans U n) =1"|
"rank (Init m n) =1"|
"rank (s1;s2) =1+ rank s2 + (rank s1 )"|
"rank (Cond mcl) =  (case mcl of [] ⇒ 1
  | mc # mcr ⇒ 1+rank (fst (snd mc)) + rank (Cond mcr)) "|
"rank  (While  m0 m1 s Q )= 1+rank(s)"
lemma rank_pos : " rank ss > 0" 
apply (induct ss, auto) 
by (smt One_nat_def Suc_less_eq le_imp_less_Suc list.case(1) list.case(2) list.exhaust monoid_add_class.add.left_neutral monoid_add_class.add.right_neutral not_le order_refl plus_nat.simps(2) rank.simps(5) trans_le_add1 trans_le_add2)
primrec wh_n::"(Mat⇒Mat) ⇒Mat⇒Mat⇒nat⇒Mat"where
"wh_n ff m1 p 0=p"|
"wh_n ff m1 p (Suc n) =ff (mat_mult (mat_mult m1 (wh_n ff m1 p n)) (dag m1))"
primrec while_n::"(Mat⇒Mat)⇒Mat⇒Mat⇒Mat⇒nat⇒Mat"where
"while_n  ff m0 m1 p 0 =zero"|
"while_n  ff m0 m1 p (Suc n) =mat_add (u m0 p) (while_n  ff m0 m1 (ff (u m1 p)) n)"



(*the denotational semantics of quantum programs  *)
function denoFun::"com⇒Mat⇒Mat" where
"denoFun SKIP p=p"|
"denoFun (Utrans U n) p=mat_mult (mat_mult U p) (dag U)"|
"denoFun (Init m n) p=sum (h m) f p "|
"denoFun (s1;s2) p= denoFun s2 (denoFun s1  p )"|
"denoFun (Cond mcl) p=  (case mcl of [] ⇒ zero
  | mc # mcr ⇒ mat_add (denoFun((fst (snd mc))) (u (fst mc) p) ) (denoFun (Cond mcr) p)) "| 
"denoFun (While m0 m1 s Q) p =(if (∀i j. convergent (λn. Rep_matrix (while_n (λa. denoFun s a) m0 m1 p n) i j)) then 
             (Abs_matrix (λi j. (lim (λ n. (Rep_matrix (while_n (λa. denoFun s a) m0 m1 p n) i j)))))
                            else   (denoFun s p))"
by  pat_completeness auto 
termination 
 apply (relation "measure (λ(c,m).rank c)",auto )
 done
 lemma rho: "positive a⟹positive (u m a)"
by (metis a1 less3 rho_zero u_def)
 fun rankf :: "com⇒nat" where
"rankf SKIP =1"|
"rankf (Utrans U n) =1"|
"rankf (Init m n) =1"|
"rankf (s1;s2) =1+ rankf s2 + (rankf s1 )"|
"rankf (Cond mcl) =  (case mcl of [] ⇒ 1
  | mc # mcr ⇒ 1+rankf (fst (snd mc)) + rankf (Cond mcr)) "|
"rankf  (While  m0 m1 s Q )= 1 + rankf s"

lemma wellDefined_aux: "(x, xa, xb) ∈ set mcl ⟹
       (xc, xd) ∈ Basic_BNFs.snds (x, xa, xb) ⟹
       xe ∈ Basic_BNFs.fsts (xc, xd) ⟹ rankf xe < (case mcl of [] ⇒ 1 | mc # mcr ⇒ 1 + rankf (fst (snd mc)) + rankf (Cond mcr))"
apply (induct mcl, auto)
by (metis fst_conv fsts.cases not_add_less1 not_less_eq sndI snds.cases)


(*the conditions that the commands should meet iff they are well-defined  *)
function wellDefined :: "com⇒bool" where
"wellDefined SKIP =True"|
"wellDefined (Utrans a n) = (UMat a)"|
"wellDefined (Init m n) =((sum_1 (h m) f =I)∧(sum_2 (h m) f=I))"|
"wellDefined (s1;s2) = (wellDefined (s1) & wellDefined (s2))"|
"wellDefined (Cond mcl) = ((M_sum mcl=I) ∧ 
(∀a aa b aaa ba xaaa. (a, aa, b) ∈ set mcl ⟶
       (aaa, ba) ∈ Basic_BNFs.snds (a, aa, b) ⟶
       xaaa ∈ Basic_BNFs.fsts (aaa, ba) ⟶ wellDefined xaaa))"|
"wellDefined  (While  m0 m1 s Q )=((mat_add (mat_mult (dag m0) m0)  (mat_mult (dag m1) m1) =I)  ∧ (wellDefined s)  )  "
by  pat_completeness auto
termination 
apply (relation "measure (λ(c).rankf c)", auto)
apply (rule wellDefined_aux, auto)
done
lemma au:" positive (denoFun s1 a) ⟹∀a. positive a⟶ positive (denoFun s2 a) ⟹ positive a ⟶positive (denoFun s2 (denoFun s1 a))"
apply auto
done
lemma init_rho: "positive a ⟹ positive (sum list f a)"
apply(induct list,auto)
by (metis a1 less3 less6 rho_zero zero_add)
lemma cond_rho:" (∀a aa b aaa ba xaaa.
∀d. positive d ⟶ (a, aa, b) ∈ set x ⟶  (aaa, ba) ∈ Basic_BNFs.snds (a, aa, b) ⟶
               xaaa ∈ Basic_BNFs.fsts (aaa, ba) ⟶ positive (denoFun xaaa d)) ⟹ ∀d. positive d ⟶
        positive   (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (denoFun (fst (snd mc)) (u (fst mc) d)) (denoFun (Cond mcr) d))"
apply(induct x,auto)
apply (metis a1 less3 rho_zero zero_mult_l)
apply(drule_tac x="d"in spec)
apply(rule c1)
prefer 2
apply(auto)
apply(drule_tac x="a" in spec)
apply(subgoal_tac "positive (u a d)")
prefer 2
using rho apply blast
apply(drule_tac x="aa"in spec)
apply(drule_tac x="b"in spec)
apply(drule_tac x="aa"in spec)
apply(drule_tac x="b"in spec)
apply(drule_tac x="aa"in spec)
apply(drule_tac x="u a d"in spec,auto)
apply (simp add: snds.simps)+
apply (simp add: fsts.simps)+
done
lemma aux7:"∀ n. ff n=(L::real)⟹lim ff =L"
apply(rule limI)
apply(rule increasing_tendsto)
apply auto
done
lemma obvious:" ∀ j. infinite ≤ j⟶  Rep_matrix A j i=0"
by (meson dual_order.trans nrows nrows_max)
lemma obvious1:" ∀ i. infinite ≤ i⟶  Rep_matrix A j i=0"
by (meson dual_order.trans ncols ncols_max)
lemma tendsto_and:"convergent gg⟹convergent ff⟹lim (λx. (ff x::real)+gg x) =lim ff+lim gg"
proof -
  assume a1: "convergent gg"
  assume a2: "convergent ff"
  obtain rr :: "(nat ⇒ real) ⇒ real" where
    f3: "⋀f r fa. (¬ f ----> (r∷real) ∨ convergent f) ∧ (¬ convergent fa ∨ fa ----> rr fa)"
    using convergent_def by moura
  hence "⋀f r. ¬ f ----> r ∨ r = rr f"
    using LIMSEQ_unique by blast
  hence "rr (λn. ff n + gg n) = rr ff + rr gg"
    using f3 a2 a1 by (metis (no_types) tendsto_add)
  thus ?thesis
    using f3 a2 a1 by (metis (no_types) LIMSEQ_unique convergent_LIMSEQ_iff tendsto_add)
qed
lemma  tendsto:
  "(gg ----> a)  ⟹ ((λx. (n::real)* (gg x)) ----> n*a) "
by (simp add: bounded_linear.tendsto bounded_linear_mult_right)
lemma  tendsto_dual:
  "(gg ----> a)  ⟹ ((λx.  (gg x)*(n::real)) ----> n*a) "
  apply(subgoal_tac "(gg ----> a)  ⟹ (λx.  (gg x)*(n::real)) =(λx. (n::real)* (gg x))")
  apply auto
 by (simp add: bounded_linear.tendsto bounded_linear_mult_right)
lemma  tendsto1:
  "convergent gg⟹(n::real)*(lim gg) =lim (λx. n*(gg x) )"
  by (metis convergent_def limI tendsto)
lemma  tendsto1_dual:
  "convergent gg⟹(lim gg)*(n::real) =lim (λx. (gg x)*n )"
  apply(subgoal_tac "convergent gg⟹lim (λx. (gg x)*n ) =lim (λx. n*(gg x) )",auto)
  apply(subgoal_tac "n*lim gg=lim (λx. n * gg x)")
  apply (simp add: mult.commute)
apply (simp add: tendsto1)
by (simp add: mult.commute)
lemma tendsto2:"convergent gg⟹convergent (λn. (x::real)* (gg n))"
using bounded_linear.convergent bounded_linear_mult_right by auto
lemma tendsto2_dual:"convergent gg⟹convergent (λn.  (gg n)*(x::real))"
using bounded_linear.convergent bounded_linear_mult_left by auto
lemma aux13:" ∀i j. convergent (λn. Rep_matrix (B n) i j) ⟹
         convergent (λxb. foldseq_transposed op + (λk. Rep_matrix A x k * Rep_matrix (B xb) k xa) m)"
         apply(induct m,auto)
         apply(drule_tac x="0" in spec)
         apply(drule_tac x="xa" in spec)
         apply(rule tendsto2,auto)
         apply(rule convergent_add,auto)
          apply(drule_tac x="Suc m" in spec)
          apply(drule_tac x="xa" in spec)
         apply(rule tendsto2,auto)
         done
lemma aux13_dual:" ∀i j. convergent (λn. Rep_matrix (B n) i j) ⟹
         convergent (λxb. foldseq_transposed op + (λk.  Rep_matrix (B xb) xa  k *Rep_matrix A  k x ) m)"
         apply(induct m,auto)
         apply(drule_tac x="xa" in spec)
         apply(drule_tac x="0" in spec)
         apply(rule tendsto2_dual,auto)
         apply(rule convergent_add,auto)
          apply(drule_tac x="xa" in spec)
          apply(drule_tac x="Suc m" in spec)
         apply(rule tendsto2_dual,auto)
         done
lemma aux12:" ∀i j. convergent (λn. Rep_matrix (B n) i j) ⟹
    foldseq_transposed op + (λk. lim (λn. Rep_matrix A x k * Rep_matrix (B n) k xa)) m =
    lim (λn. foldseq_transposed op + (λk. Rep_matrix A x k * Rep_matrix (B n) k xa) m)"
    apply(induct m,auto)
    apply(subgoal_tac "lim (λn. foldseq_transposed op + (λk. Rep_matrix A x k * Rep_matrix (B n) k xa) m + Rep_matrix A x (Suc m) * Rep_matrix (B n) (Suc m) xa) =
        lim (λn. foldseq_transposed op + (λk. Rep_matrix A x k * Rep_matrix (B n) k xa) m) 
        +lim (λn. Rep_matrix A x (Suc m) * Rep_matrix (B n) (Suc m) xa)")
   apply auto
   apply(rule tendsto_and)
    apply(drule_tac x="Suc m" in spec)
    apply(drule_tac x="xa" in spec)
    apply(rule tendsto2,auto)
    apply(simp add:aux13)
    done
lemma aux10:"∀ i j. convergent (λn. Rep_matrix (B n) i j) ⟹ foldseq op + (λk. lim (λn. Rep_matrix A x k * Rep_matrix (B n) k xa)) m=
      lim (λn. ( foldseq op+  (λk. Rep_matrix A x k * Rep_matrix (B n) k xa) m))"
      apply(subgoal_tac " foldseq_transposed op + (λk. lim (λn. Rep_matrix A x k * Rep_matrix (B n) k xa)) m =
                           foldseq op + (λk. lim (λn. Rep_matrix A x k * Rep_matrix (B n) k xa)) m")
      prefer 2
      apply (simp add: associative_def foldseq_assoc)
      apply(subgoal_tac "(λn. foldseq op + (λk. Rep_matrix A x k * Rep_matrix (B n) k xa) m) =
                      (λn. foldseq_transposed op + (λk. Rep_matrix A x k * Rep_matrix (B n) k xa) m)")
      prefer 2
      apply(rule ext)
      apply (simp add: associative_def foldseq_assoc)
      apply(subgoal_tac " foldseq_transposed op + (λk. lim (λn. Rep_matrix A x k * Rep_matrix (B n) k xa)) m=
      lim (λn. ( foldseq_transposed op+  (λk. Rep_matrix A x k * Rep_matrix (B n) k xa) m)) ")
      apply simp
      by(simp add:aux12)
lemma aux10_dual:"∀ i j. convergent (λn. Rep_matrix (B n) i j) ⟹    foldseq op + (λk. lim (λn. Rep_matrix (B n) x k * Rep_matrix A k xa)) m =
    lim (λn. foldseq op + (λk. Rep_matrix (B n) x k * Rep_matrix A k xa) m) "
    apply(subgoal_tac "foldseq_transposed op + (λk. lim (λn. Rep_matrix (B n) x k * Rep_matrix A k xa)) m =
    lim (λn. foldseq_transposed op + (λk. Rep_matrix (B n) x k * Rep_matrix A k xa) m) ")
    apply (simp add: associative_def foldseq_assoc)
    apply(induct m,auto)
    apply(subgoal_tac " lim (λn. foldseq_transposed op + (λk. Rep_matrix (B n) x k * Rep_matrix A k xa) m +
                  Rep_matrix (B n) x (Suc m) * Rep_matrix A (Suc m) xa) =
           lim (λn. foldseq_transposed op + (λk. Rep_matrix (B n) x k * Rep_matrix A k xa) m )+
            lim(λn. Rep_matrix (B n) x (Suc m) * Rep_matrix A (Suc m) xa) ",auto)
    apply(rule tendsto_and)
    apply(drule_tac x="x" in spec)
    apply(drule_tac x="Suc m" in spec)
    apply(rule tendsto2_dual,auto)
     apply(simp add:aux13_dual)
     done
lemma aux11:" foldseq op + (λk. Rep_matrix A x k * Rep_matrix B k xa)
     (max (ncols A) (nrows B)) = foldseq op + (λk. Rep_matrix A x k * Rep_matrix B k xa)
     infinite"
     apply(rule foldseq_zerotail,auto)
     apply (simp add: ncols)
     done
lemma aux9:"∀ i j. convergent (λn. Rep_matrix (B n) i j) ⟹ Rep_matrix (mult_matrix op * op + A (Abs_matrix (λi j. lim (λn. Rep_matrix (B n) i j)))) x xa =
            lim (λn. Rep_matrix (mult_matrix op * op + A (B n)) x xa)"
    apply(simp add:mult_matrix_def)
    apply(simp add:mult_matrix_n_def)
    apply(simp add:aux11)
    apply(subgoal_tac "Rep_matrix  (Abs_matrix
       (λj i. foldseq op + (λk. Rep_matrix A j k * Rep_matrix (Abs_matrix (λi j. lim (λn. Rep_matrix (B n) i j))) k i)
             infinite)) =  (λj i. foldseq op + (λk. Rep_matrix A j k * Rep_matrix (Abs_matrix (λi j. lim (λn. Rep_matrix (B n) i j))) k i)
              infinite)")
    prefer 2
    apply(rule RepAbs_matrix)
    apply(rule_tac x="infinite " in exI,auto) 
    apply(rule foldseq_zero,auto)
    using obvious apply blast
    apply(rule_tac x="infinite " in exI,auto)
    apply(rule foldseq_zero,auto)
   using obvious1 apply blast
   apply(subgoal_tac "(λk. Rep_matrix A x k * Rep_matrix (Abs_matrix (λi j. lim (λn. Rep_matrix (B n) i j))) k xa) =
          (λk. Rep_matrix (Abs_matrix (λi j. Rep_matrix A x k * lim (λn. Rep_matrix (B n) i j))) k xa) " )
   prefer 2
  apply(rule ext)
  apply(subgoal_tac " Rep_matrix (Abs_matrix (λi j. Rep_matrix A x k * lim (λn. Rep_matrix (B n) i j))) =
       (λi j. Rep_matrix A x k * lim (λn. Rep_matrix (B n) i j))",auto)
  prefer 2
  apply(rule RepAbs_matrix)
  apply(rule_tac x="infinite " in exI,auto)
  apply(rule aux7)
  apply (simp add: obvious)
  apply(rule_tac x="infinite " in exI,auto)
  apply (simp add: aux7 obvious1)
  apply(subgoal_tac " Rep_matrix (Abs_matrix (λi j. lim (λn. Rep_matrix (B n) i j))) = (λi j. lim (λn. Rep_matrix (B n) i j))",auto)
   apply(rule RepAbs_matrix)
  apply(rule_tac x="infinite " in exI,auto)
  apply(rule aux7)
  apply (simp add: obvious)
  apply(rule_tac x="infinite " in exI,auto)
  apply(rule aux7)
  apply (simp add: obvious1)
  apply(subgoal_tac "(λn. Rep_matrix (Abs_matrix (λj i. foldseq op + (λk. Rep_matrix A j k * Rep_matrix (B n) k i) infinite)) x xa) =
    (λn.  foldseq op + (λk. Rep_matrix A x k * Rep_matrix (B n) k xa) infinite)")
  prefer 2
  apply(rule ext)
  apply(subgoal_tac "Rep_matrix (Abs_matrix (λj i. foldseq op + (λk. Rep_matrix A j k * Rep_matrix (B n) k i) infinite)) =
         (λj i. foldseq op + (λk. Rep_matrix A j k * Rep_matrix (B n) k i) infinite)")
  prefer 2
  apply(rule RepAbs_matrix)
  apply(rule_tac x="infinite " in exI,auto)
   apply (rule  foldseq_zero,auto)
using obvious apply blast
  apply(rule_tac x="infinite " in exI,auto)
    apply (rule  foldseq_zero,auto)
  using obvious1 apply blast
  apply(subgoal_tac "(λk. Rep_matrix (Abs_matrix (λi j. Rep_matrix A x k * lim (λn. Rep_matrix (B n) i j))) k xa) =
    (λk.  Rep_matrix A x k * lim (λn. Rep_matrix (B n) k xa))")
  prefer 2
  apply(rule ext)
  apply(subgoal_tac "Rep_matrix (Abs_matrix (λi j. Rep_matrix A x k * lim (λn. Rep_matrix (B n) i j))) =
          (λi j. Rep_matrix A x k * lim (λn. Rep_matrix (B n) i j))")
  prefer 2
    apply(rule RepAbs_matrix)
  apply(rule_tac x="infinite " in exI,auto)
using aux7 obvious apply auto[1]
  apply(rule_tac x="infinite " in exI,auto)
  apply (simp add: aux7 obvious1)
  apply(subgoal_tac "(λk. Rep_matrix A x k * lim (λn. Rep_matrix (B n) k xa)) =
        (λk.  lim (λn. Rep_matrix A x k *Rep_matrix (B n) k xa))")
  prefer 2
  apply(rule ext)
  apply(rule tendsto1,auto)
  apply(simp add:aux10)
  done
lemma aux9_dual:" ∀i j. convergent (λn. Rep_matrix (B n) i j) ⟹ Rep_matrix (mult_matrix op * op + (Abs_matrix (λi j. lim (λn. Rep_matrix (B n) i j))) A) x xa =
            lim (λn. Rep_matrix (mult_matrix op * op + (B n) A) x xa)"
    apply(simp add:mult_matrix_def)
    apply(simp add:mult_matrix_n_def)
    apply(simp add:aux11) 
    apply(subgoal_tac " Rep_matrix (Abs_matrix (λj i. foldseq op + (λk. Rep_matrix (Abs_matrix (λi j. lim (λn. Rep_matrix (B n) i j))) j k * Rep_matrix A k i) infinite)) =
      (λj i. foldseq op + (λk. Rep_matrix (Abs_matrix (λi j. lim (λn. Rep_matrix (B n) i j))) j k * Rep_matrix A k i) infinite)")
     prefer 2
    apply(rule RepAbs_matrix)
    apply(rule_tac x="infinite " in exI,auto)
    apply(rule foldseq_zero,auto)
    using obvious apply blast
     apply(rule_tac x="infinite " in exI,auto)
    apply(rule foldseq_zero,auto)
   using obvious1 apply blast
   apply(subgoal_tac "(λk. Rep_matrix (Abs_matrix (λi j. lim (λn. Rep_matrix (B n) i j))) x k * Rep_matrix A k xa) =
     (λk. Rep_matrix (Abs_matrix (λi j. lim (λn. Rep_matrix (B n) i j)* Rep_matrix A k xa)) x k ) ")
   prefer 2
   apply(rule ext)
   apply(subgoal_tac "Rep_matrix (Abs_matrix (λi j. lim (λn. Rep_matrix (B n) i j) * Rep_matrix A k xa)) =
             (λi j. lim (λn. Rep_matrix (B n) i j) * Rep_matrix A k xa)",auto)
   prefer 2
  apply(rule RepAbs_matrix)
  apply(rule_tac x="infinite " in exI,auto)
    apply(rule aux7)
  apply (simp add: obvious)
    apply(rule_tac x="infinite " in exI,auto)
  apply (simp add: aux7 obvious1)
  apply(subgoal_tac "Rep_matrix (Abs_matrix (λi j. lim (λn. Rep_matrix (B n) i j))) =
       (λi j. lim (λn. Rep_matrix (B n) i j))",auto)
     apply(rule RepAbs_matrix)
  apply(rule_tac x="infinite " in exI,auto)
  apply(rule aux7)
  apply (simp add: obvious)
  apply(rule_tac x="infinite " in exI,auto)
  apply(rule aux7)
  apply (simp add: obvious1)
  apply(subgoal_tac "(λn. Rep_matrix (Abs_matrix (λj i. foldseq op + (λk. Rep_matrix (B n) j k * Rep_matrix A k i) infinite)) x xa) =
    (λn.  foldseq op + (λk. Rep_matrix (B n) x k * Rep_matrix A k xa) infinite)")
  prefer 2
  apply(rule ext)
  apply(subgoal_tac "Rep_matrix (Abs_matrix (λj i. foldseq op + (λk. Rep_matrix (B n) j k * Rep_matrix A k i) infinite)) =
        (λj i. foldseq op + (λk. Rep_matrix (B n) j k * Rep_matrix A k i) infinite)")
  prefer 2
  apply(rule RepAbs_matrix)
  apply(rule_tac x="infinite " in exI,auto)
   apply (rule  foldseq_zero,auto)
using obvious apply blast
  apply(rule_tac x="infinite " in exI,auto)
    apply (rule  foldseq_zero,auto)
  using obvious1 apply blast
  apply(subgoal_tac "(λk. Rep_matrix (Abs_matrix (λi j. lim (λn. Rep_matrix (B n) i j) * Rep_matrix A k xa)) x k) =
    (λk.  lim (λn. Rep_matrix (B n) x k) * Rep_matrix A k xa)")
    prefer 2
  apply(rule ext)
  apply(subgoal_tac "Rep_matrix (Abs_matrix (λi j. lim (λn. Rep_matrix (B n) i j) * Rep_matrix A k xa)) =
        (λi j. lim (λn. Rep_matrix (B n) i j) * Rep_matrix A k xa)")
  prefer 2
      apply(rule RepAbs_matrix)
  apply(rule_tac x="infinite " in exI,auto)
using aux7 obvious apply auto[1]
  apply(rule_tac x="infinite " in exI,auto)
  apply (simp add: aux7 obvious1)
  apply(subgoal_tac "(λk. lim (λn. Rep_matrix (B n) x k) * Rep_matrix A k xa) =
    (λk. lim (λn. Rep_matrix (B n) x k  * Rep_matrix A k xa))")
    prefer 2
  apply(rule ext)
  apply(rule tendsto1_dual,auto)
   apply(simp add:aux10_dual)
   done
  (* A*lim (B n) = lim (A * (B n) ) *)
lemma aux3:"∀i j. convergent (λn. Rep_matrix (B n) i j) ⟹mat_mult A (Abs_matrix (λi j. lim (λn. Rep_matrix  (B n) i j)))=Abs_matrix (λi j. lim (λn. Rep_matrix (mat_mult A (B n)) i j)) "
apply(simp add:mat_mult_def times_matrix_def )
apply(subst Rep_matrix_inject[symmetric])
apply(rule ext)+
apply(subgoal_tac "Rep_matrix (Abs_matrix (λi j. lim (λn. Rep_matrix (mult_matrix op * op + A (B n)) i j))) =
       (λi j. lim (λn. Rep_matrix (mult_matrix op * op + A (B n)) i j)) ")
prefer 2
 apply(rule RepAbs_matrix)
 apply(rule_tac x="infinite " in exI,auto)
 apply(rule aux7)
 apply (simp add: obvious)
 apply(rule_tac x="infinite " in exI,auto)
 apply (simp add: obvious1)
 apply (simp add: aux7)
 apply(simp add:aux9)
done
  (* lim (B n)*A = lim ( (B n)*A ) *)
lemma aux4:"∀i j. convergent (λn. Rep_matrix (B n) i j) ⟹mat_mult  (Abs_matrix (λi j. lim (λn. Rep_matrix  (B n) i j))) A=
     Abs_matrix (λi j. lim (λn. Rep_matrix (mat_mult  (B n) A) i j)) "
apply(simp add:mat_mult_def times_matrix_def )
apply(subst Rep_matrix_inject[symmetric])
apply(rule ext)+
apply(subgoal_tac " Rep_matrix (Abs_matrix (λi j. lim (λn. Rep_matrix (mult_matrix op * op + (B n) A) i j))) =
   (λi j. lim (λn. Rep_matrix (mult_matrix op * op + (B n) A) i j))",auto)
prefer 2
 apply(rule RepAbs_matrix)
 apply(rule_tac x="infinite " in exI,auto)
  apply(rule aux7)
   apply (simp add: obvious)
  apply(rule_tac x="infinite " in exI,auto)
 apply (simp add: obvious1)
apply (simp add: limI)
apply(simp add:aux9_dual)
done

lemma aux6:"Rep_matrix (Abs_matrix (λi j. lim (λn. Rep_matrix (A n) i j))) =(λi j. (lim (λn. Rep_matrix (A n) i j)))"
apply(rule RepAbs_matrix)
apply(rule_tac x="infinite " in exI,auto)
apply(rule_tac ff="λn. Rep_matrix (A n) j i"in  aux7,auto)
apply (metis max2 max_absorb1 nrows nrows_max)
apply(rule_tac x="infinite " in exI,auto)
apply(rule_tac ff="λn. Rep_matrix (A n) j i"in  aux7,auto)
using ncols_le ncols_max by blast

lemma aux5:"∀i j. convergent (λn. Rep_matrix (A n) i j) ⟹ ∀n. Rep_matrix (A n) 0 0≥0 ⟹
          Rep_matrix (Abs_matrix (λi j. lim (λn. Rep_matrix (A n) i j))) 0 0≥0"
        apply(simp add:aux6)
        apply(rule_tac a="0" and f="λn. Rep_matrix (A n) 0 0"and F="sequentially" in  tendsto_le_const)
        apply auto
        apply(subgoal_tac "convergent (λn. Rep_matrix (A n) 0 0) ")
        apply (simp add: convergent_LIMSEQ_iff)
        by auto
lemma aux14:"∀i j. convergent (λn. Rep_matrix (A n) i j) ⟹ convergent (λn. Rep_matrix  (mat_mult v (A n))  i j)"
      apply(simp add:mat_mult_def)
       apply(simp add:times_matrix_def mult_matrix_def )
       apply(simp add:mult_matrix_n_def)
       apply(simp add:aux11)
       apply(subgoal_tac "(λn. Rep_matrix (Abs_matrix (λj i. foldseq op + (λk. Rep_matrix v j k * Rep_matrix (A n) k i) infinite)) i j) =
         (λn.  (λj i. foldseq op + (λk. Rep_matrix v j k * Rep_matrix (A n) k i) infinite) i j)",auto)
       prefer 2
       apply(rule ext)
       apply(subgoal_tac " Rep_matrix (Abs_matrix (λj i. foldseq op + (λk. Rep_matrix v j k * Rep_matrix (A n) k i) infinite)) =
          (λj i. foldseq op + (λk. Rep_matrix v j k * Rep_matrix (A n) k i) infinite)",auto)      
      apply(rule RepAbs_matrix)
      apply(rule_tac x="infinite " in exI,auto)
      apply (simp add: foldseq_zero obvious)
      apply(rule_tac x="infinite " in exI,auto)
      apply (simp add: foldseq_zero obvious1)
      apply(subgoal_tac " convergent (λn. foldseq_transposed op + (λk. Rep_matrix v i k * Rep_matrix (A n) k j) infinite) ")
      apply (simp add: associative_def foldseq_assoc)
      apply(simp add:aux13)
      done
lemma aux15:"∀i j. convergent (λn. Rep_matrix (A n) i j) ⟹
             convergent (λn. Rep_matrix (mat_mult  (A n) v) i j)"
        apply(simp add:mat_mult_def)
       apply(simp add:times_matrix_def mult_matrix_def )
       apply(simp add:mult_matrix_n_def)
       apply(simp add:aux11)
       apply(subgoal_tac "(λn. Rep_matrix (Abs_matrix (λj i. foldseq op + (λk. Rep_matrix (A n) j k * Rep_matrix v k i) infinite)) i j) =
            (λn. (λj i. foldseq op + (λk. Rep_matrix (A n) j k * Rep_matrix v k i) infinite) i j)",auto)
       prefer 2
       apply(rule ext)
       apply(subgoal_tac " Rep_matrix (Abs_matrix (λj i. foldseq op + (λk. Rep_matrix (A n) j k * Rep_matrix v k i) infinite)) =
           (λj i. foldseq op + (λk. Rep_matrix (A n) j k * Rep_matrix v k i) infinite)  ",auto)
      apply(rule RepAbs_matrix)
      apply(rule_tac x="infinite " in exI,auto)
      apply (simp add: foldseq_zero obvious)
      apply(rule_tac x="infinite " in exI,auto)
      apply (simp add: foldseq_zero obvious1)
      apply(subgoal_tac "convergent (λn. foldseq_transposed op + (λk. Rep_matrix (A n) i k * Rep_matrix v k j) infinite) ")
      apply (simp add: associative_def foldseq_assoc)
      apply(simp add:aux13_dual)
      done
lemma aux1:"∀i j. convergent (λn. Rep_matrix (A n) i j) ⟹∀n v. Rep_matrix (mat_mult (mat_mult v (A n)) (dag v)) 0 0≥0 ⟹
       ∀ v. Rep_matrix (mat_mult (mat_mult v (Abs_matrix (λi j. (lim (λ n. (Rep_matrix (A n) i j))) ))) (dag v)) 0 0≥0"
       apply auto
       apply(simp add:aux3)
       apply(subgoal_tac "  0 ≤ Rep_matrix  (Abs_matrix (λi j. lim (λn. Rep_matrix (  mat_mult (mat_mult v (A n)) (dag v)  ) i j))) 0 0")
       apply (simp add: aux14 aux4)
       apply(rule aux5,auto)
       apply(simp add:aux14 aux15)
       done
   (*positive (A n) ⟹ positive lim (A n)*)
lemma aux:"∀i j. convergent (λn. Rep_matrix (A n) i j) ⟹∀n. positive (A n) ⟹positive (Abs_matrix (λi j. (lim (λ n. (Rep_matrix (A n) i j))) ))"
apply(rule posi_decide)
prefer 2
apply (simp add: posi aux1)
apply(simp add:dag_def transpose_matrix_def)
apply(subgoal_tac "(λi j. lim (λn. Rep_matrix (A n) i j)) =(transpose_infmatrix (Rep_matrix (Abs_matrix (λi j. lim (λn. Rep_matrix (A n) i j)))))")
apply simp
apply(rule ext)+
apply(simp add:transpose_infmatrix_def)
apply(subgoal_tac " Rep_matrix (Abs_matrix (λi j. lim (λn. Rep_matrix (A n) i j))) j i =
        (λi j. lim (λn. Rep_matrix (A n) i j)) j i ")
prefer 2
apply (simp add: aux6)
apply auto
apply(subgoal_tac "  (λn. Rep_matrix (A n) i j) =  (λn. Rep_matrix (A n) j i) ")
apply simp
by (metis eq tr_pow_aux3)
lemma aux_advance:" ∀n. positive (A n) ⟹∃B.∀n. Tr (A n) ≤B ⟹ ∀n. less (A n) (A (Suc n)) 
               ⟹positive (Abs_matrix (λi j. (lim (λ n. (Rep_matrix (A n) i j))) ))"
apply(rule aux,auto)
using convergent by blast

lemma lim_tr_aux:" foldseq op + (λk. Rep_matrix A k k) (max (nrows A) (ncols A)) =
                   foldseq op + (λk. Rep_matrix A k k) infinite"
     apply(rule foldseq_zerotail,auto)
     apply (simp add: ncols)
     done
lemma lim_tr_aux2:" ∀i j. convergent (λn. Rep_matrix (A n) i j) ⟹ convergent (λn. foldseq_transposed op + (λk. Rep_matrix (A n) k k) m)"
    apply(induct m,auto)
    apply(rule convergent_add,auto)
    done
lemma lim_tr_aux1:" ∀i j. convergent (λn. Rep_matrix (A n) i j) ⟹
    lim (λn. foldseq op + (λk. Rep_matrix (A n) k k) m) = foldseq op + (λk. lim (λn. Rep_matrix (A n) k k)) m"
    apply(subgoal_tac " lim (λn. foldseq_transposed op + (λk. Rep_matrix (A n) k k) m) = foldseq_transposed op + (λk. lim (λn. Rep_matrix (A n) k k)) m")
    apply (simp add: associative_def foldseq_assoc)
    apply(induct m,auto)
    apply(cut_tac ff="(λn. foldseq_transposed op + (λk. Rep_matrix (A n) k k) m)" and gg="(λn. Rep_matrix (A n) (Suc m) (Suc m))"in  tendsto_and)
    prefer 3
    apply auto
    apply(simp add:lim_tr_aux2)
    done
    (*lim tr(A n) =tr (lim (A n))*)
lemma lim_tr:"∀i j. convergent (λn. Rep_matrix (A n) i j) ⟹lim (λn. Tr(A n)) =Tr (Abs_matrix (λi j. (lim (λ n. (Rep_matrix (A n) i j)))))"
apply(simp add:Tr_def)
apply(simp add:tr_def)
apply(simp add:lim_tr_aux)
apply(subgoal_tac "(λk. Rep_matrix (Abs_matrix (λi j. lim (λn. Rep_matrix (A n) i j))) k k) =
       (λk. lim (λn. Rep_matrix (A n) k k))",auto)
prefer 2
apply(rule ext)
apply(subgoal_tac "Rep_matrix (Abs_matrix (λi j. lim (λn. Rep_matrix (A n) i j))) =
                      (λi j. lim (λn. Rep_matrix (A n) i j))",auto)
apply(rule RepAbs_matrix)
apply(rule_tac x="infinite " in exI,auto)
apply(rule aux7)
apply (simp add: obvious)
apply(rule_tac x="infinite " in exI,auto)
apply (simp add: aux7 obvious1)
apply(simp add:lim_tr_aux1)
done
  (*lim tr ((A n)*B) =tr (lim (A n)*B)*)
lemma lim_Tr:"∀i j. convergent (λn. Rep_matrix (A n) i j) ⟹lim (λn. Tr( mat_mult B (A n)  )) =Tr (mat_mult B (Abs_matrix (λi j. (lim (λ n. (Rep_matrix (A n) i j))))) )"
by (simp add: aux14 lim_tr aux3)
lemma fuck_aux:"convergent X⟹X---->(L::real) ⟹∀n. X n≤c⟹L≤c"
using limI lim_le by blast
lemma haha:"∀n. ((X n)::real) ≤X (Suc n) ⟹∃c. ∀n.  X n≤c⟹convergent X"
using BseqI2 Bseq_mono_convergent lift_Suc_mono_le by blast
lemma important_aux:" ∀i j. convergent (λn. Rep_matrix (A n) i j) ⟹ positive P ⟹ ∀n. positive (A n) ⟹
   ∀n. Matrix.less (A n) (A (Suc n)) ⟹ ∀n. Tr (mat_mult P (A n)) ≤ c ⟹ convergent (λn. Tr (mat_mult P (A n)))"
    apply(rule haha,auto)
    apply(subgoal_tac "Tr (mat_sub (mat_mult P (A (Suc n))) (mat_mult P (A n))) ≥0 ")
    apply(simp add:tr_allo1)
    apply(subgoal_tac " 0 ≤ Tr  (mat_mult P (mat_sub (A (Suc n)) (A n)) ) ")
    apply (simp add: mult_sub_allo2)
    apply(rule less44,auto)
    by (simp add: less_def)
    (*    ∀n.Tr (X n)*P≤c⟹Tr (lim X n)*P≤c         *)
 lemma important:"∀i j. convergent (λn. Rep_matrix (A n) i j) ⟹positive P⟹∀n. (positive (A n))  ⟹∀n. less (A n) (A (Suc n))
       ⟹∀n. Tr (mat_mult P (A n)) ≤c⟹Tr (mat_mult P (Abs_matrix (λi j. (lim (λ n. (Rep_matrix (A n) i j))))) ) ≤c"
       apply(subgoal_tac "lim (λn. Tr( mat_mult P (A n))) ≤c")
       apply (simp add: lim_Tr)
       apply(rule fuck_aux,auto)
       prefer 2
       apply(subgoal_tac " convergent (λn. Tr (mat_mult P (A n)))")
       using convergent_LIMSEQ_iff apply blast
       using important_aux apply blast
       using important_aux apply blast
       done
 lemma important1:"∀i j. convergent (λn. Rep_matrix (A n) i j)⟹∀n. (positive (A n)) ⟹∀n. less (A n) (A (Suc n))
       ⟹∀n. Tr (mat_mult I (A n)) ≤c⟹Tr (mat_mult I (Abs_matrix (λi j. (lim (λ n. (Rep_matrix (A n) i j))))) ) ≤c"
       apply(rule important,auto)
       using I_zero a1 by blast
 lemma important2:"∀i j. convergent (λn. Rep_matrix (A n) i j)⟹∀n. (positive (A n))  ⟹∀n. less (A n) (A (Suc n))
       ⟹∀n. Tr ( (A n)) ≤c⟹Tr ( (Abs_matrix (λi j. (lim (λ n. (Rep_matrix (A n) i j))))) ) ≤c"
      using Ident important1 by auto
     
 lemma important_advance:"positive P⟹∀n. (positive (A n)) ⟹∃B.∀n. Tr (A n) ≤B ⟹∀n. less (A n) (A (Suc n))
       ⟹∀n. Tr (mat_mult P (A n)) ≤c⟹Tr (mat_mult P (Abs_matrix (λi j. (lim (λ n. (Rep_matrix (A n) i j))))) ) ≤c"
       apply(rule important,auto)
       using convergent by blast
lemma temp:"Tr (sum m f ρ ) =Tr  (mat_mult ρ (sum_2 m  f) ) "
apply(induct m)
apply auto
apply (metis Ident exchange)
by (metis exchange mult_allo2 mult_exchange tr_allo)

lemma m_init:"sum_1 m  f=I⟹sum_2 m  f=I⟹Tr (sum m f ρ ) =Tr ρ"
apply(simp add:temp)
apply(subgoal_tac " Tr (mat_mult ρ I) = Tr (mat_mult I ρ ) ")
apply(simp add:Ident)
apply(simp add:exchange)
done
 lemma bb_aux:"∀a. positive a ⟶ positive (denoFun s a) ⟹
      ∀a. positive a ⟶ positive (while_n (denoFun s) x1 x2 a n) "
      apply(induct n,auto)
      using a1 less11 less3 apply blast
      apply(subgoal_tac "positive (u x2 a)")
      prefer 2
      apply (simp add: less3_aux u_def)
      apply(drule_tac x="denoFun s (u x2 a)"in spec)
      apply(drule_tac x="u x2 a"in spec,auto)
      by (simp add: c1 less3_aux u_def)
lemma bb_aux2:" ∀a. positive a ⟶ positive (denoFun s a) ⟹ ∀a. positive a ⟶
            less (while_n (denoFun s) x1 x2 a n) (mat_add (u x1 a) (while_n (denoFun s) x1 x2 (denoFun s (u x2 a)) n))"
      apply(induct n,auto)
      apply (simp add: rho rho_zero zero_add)
      apply(subgoal_tac "positive (denoFun s (u x2 a))")
      prefer 2
      using rho apply auto[1]
      apply(drule_tac x="(denoFun s (u x2 a))" in spec,auto)
      by (simp add: less1)

lemma bb_aux1:" wellDefined s⟹ ∀a. positive a ⟶ positive (denoFun s a) ⟹ ∀i j. convergent (λn. Rep_matrix (while_n (denoFun s) x1 x2 a n) i j) ⟹
       positive a ⟹ positive (Abs_matrix (λi j. lim (λn. Rep_matrix (while_n (denoFun s) x1 x2 a n) i j)))"
       apply(rule aux,auto)
       apply(simp add:bb_aux)
       done
(* a∈rhoMat⟹denoFun s a ∈rhoMat      *)
lemma bb:"wellDefined s⟹∀a. positive a⟶positive (denoFun s a)"
apply(induct s,auto)
apply(rule init_rho,auto)
apply (metis rho u_def)
apply(cut_tac cond_rho,auto)
apply(simp add:bb_aux1)
done
lemma b:"wellDefined s⟹positive a⟹positive (denoFun s a)"
apply(simp add:bb)
done
lemma bb_aux3:"wellDefined s⟹mat_add (mat_mult (dag x1) x1) (mat_mult (dag x2) x2) = I ⟹
      ∀p. positive p⟶Tr (denoFun s p) ≤Tr p⟹ ∀a. positive a ⟶ Tr (while_n (denoFun s) x1 x2 a n) ≤Tr a"  
      apply(induct n,auto)
      apply (simp add: rho_tr zero_tr)
      apply(simp add:tr_allo)
      apply(subgoal_tac "positive (denoFun s (u x2 a))")
      prefer 2
      apply (simp add: quantum_hoare_logic.b rho)
      apply(drule_tac x="(denoFun s (u x2 a))"in spec,auto)
      apply(subgoal_tac " Tr (u x1 a) + Tr (denoFun s (u x2 a))  ≤ Tr a")
      apply simp
      apply(subgoal_tac "positive (u x2 a)")
      prefer 2
      apply (simp add: rho)
      apply(drule_tac x=" (u x2 a)"in spec,auto)
      apply(subgoal_tac " Tr (u x1 a) +  Tr (u x2 a) ≤ Tr a ")
      apply simp
      apply(simp add:u_def exchange_tr)
      apply(subgoal_tac " Tr (mat_mult (mat_mult (dag x1)  x1) a) +Tr (mat_mult (mat_mult (dag x2)  x2) a) ≤ Tr a")
      apply (simp add: mult_exchange)
      by (metis Ident_dual exchange_tr mult_allo2 order_refl tr_allo)
lemma bb_aux4_aux:" (⋀a aa b  p.
               (a, aa, b) ∈ set x ⟹ positive p ⟹ Tr (denoFun aa p) ≤ Tr p) ⟹
           positive p ⟹
           ∀a aa b. (a, aa, b) ∈ set x ⟶  wellDefined aa ⟹
           Tr (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (denoFun (fst (snd mc)) (u (fst mc) p)) (denoFun (Cond mcr) p))
           ≤ Tr (mat_mult (M_sum x) p)"
           apply(induct x,auto)
           apply (simp add: zero_mult_l)
           apply(simp add:mult_allo1)
           apply(simp add:tr_allo)
           apply(subgoal_tac "positive (u a p)")
           prefer 2
           apply (simp add: rho)
           apply(subgoal_tac " Tr (denoFun aa (u a p))≤Tr (u a p)")
           prefer 2
           apply blast
           apply(subgoal_tac "Tr (u a p) =Tr (mat_mult (mat_mult (dag a) a) p)")
           prefer 2
           apply (metis exchange_tr mult_exchange u_def)
           apply(subgoal_tac " Tr (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (denoFun (fst (snd mc)) (u (fst mc) p)) (denoFun (Cond mcr) p))
               ≤ Tr (mat_mult (M_sum x) p)")
           apply simp
           by blast
lemma bb_aux4:"wellDefined s⟹∀p. positive p⟶Tr (denoFun s p) ≤Tr p" 
      apply auto
      apply(induct s,auto)
      apply (simp add: m_init)
      apply (smt Ident UMat_def exchange_tr mult_exchange)
      apply(subgoal_tac "positive (denoFun s1 p)")
      prefer 2
      apply (simp add: quantum_hoare_logic.b)
      apply(subgoal_tac "Tr (denoFun s2 (denoFun s1 p)) ≤ Tr (denoFun s1 p)")
      prefer 2
      apply simp
      apply(subgoal_tac " Tr (denoFun s1 p) ≤Tr p")
      apply linarith
      apply auto
      prefer 2
      apply(rule important2,auto)
      apply (simp add: bb_aux quantum_hoare_logic.b)
      apply (simp add: bb_aux2 quantum_hoare_logic.b)
      apply (simp add: bb_aux3)
      apply(subgoal_tac " Tr (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (denoFun (fst (snd mc)) (u (fst mc) p))
                        (denoFun (Cond mcr) p)) ≤ Tr (mat_mult (M_sum x) p)")
      apply (simp add: Ident)
      by (metis (no_types, lifting) bb_aux4_aux fst_eqD fsts.intros list.case(1) list.case(2) list.exhaust snd_eqD snds.intros)
lemma bb_aux5:"wellDefined s⟹mat_add (mat_mult (dag x1) x1) (mat_mult (dag x2) x2) = I⟹ ∀a. positive a ⟶ Tr (while_n (denoFun s) x1 x2 a n) ≤Tr a"
      apply(rule bb_aux3,auto)
      apply(simp add:bb_aux4)
      done
      (*  while_n converge    *)
lemma while_convergent:"wellDefined (While m0 m1 s Q) ⟹positive p ⟹
                 ∀i j. convergent (λn. Rep_matrix (while_n (λa. denoFun s a) m0 m1 p n) i j)"
    apply(rule convergent,auto)
    apply (simp add: bb_aux quantum_hoare_logic.b)
    apply(rule_tac x="Tr p" in exI)
    apply (simp add: bb_aux5)
    by (simp add: bb_aux2 quantum_hoare_logic.b)
lemma while_denoFun:"wellDefined (While m0 m1 s Q) ⟹positive p⟹denoFun (While m0 m1 s Q) p =
             (Abs_matrix (λi j. (lim (λ n. (Rep_matrix (while_n (λa. denoFun s a) m0 m1 p n) i j))))) "
       apply auto
       by (simp add: while_convergent)
(*the definition of valid *)
definition valid::"Mat⇒com⇒Mat⇒bool" where
"  valid P S Q= (∀ρ. positive ρ⟶ Tr (mat_mult P ρ)<= Tr (mat_mult Q (denoFun S ρ))+Tr ρ-Tr (denoFun S ρ))"
(*svalid is equal to valid ,just for simplication*)
definition svalid::"Mat⇒com⇒Mat⇒bool"where
"svalid P S Q=(∀ ρ .positive ρ⟶ Tr (mat_mult (mat_sub I Q) (denoFun S ρ)) <= Tr (mat_mult (mat_sub I P) ρ) )"
lemma eq_valid:"svalid P S Q  ⟹valid P S Q"
apply(simp add:valid_def)
apply(simp add:svalid_def)
apply(simp add:mult_sub_allo1)
apply(simp add:tr_allo1)
apply(simp add:Ident)
apply auto
done
lemma eq_valid2:"valid P S Q⟹svalid P S Q"
apply(simp add:valid_def)
apply(simp add:svalid_def)
apply(simp add:mult_sub_allo1)
apply(simp add:tr_allo1)
apply(simp add:Ident)
apply auto
done
 
lemma b1:" (mat_mult (mat_mult (mat_mult a b) c) d) =mat_mult (mat_mult a b) (mat_mult c d)"
apply (simp add:mult_exchange)
done
lemma b2:" (mat_mult (mat_mult b d) (mat_mult a c)) =mat_mult (mat_mult (mat_mult b d) a) c"
apply (simp add:mult_exchange)
done
lemma b3:" Tr (mat_mult (mat_mult (mat_mult e  b) d) c)=Tr (mat_mult b (mat_mult (mat_mult d c) e ))"
apply(simp add:b1)
apply(simp add:exchange)
apply(simp add:b2)
apply(simp add:exchange)
done
lemma b4:"mat_mult (dag U) (mat_mult U ρ) =mat_mult(mat_mult (dag U) U) ρ"
apply(simp add:mult_exchange)
done

lemma Initfact: "positive ρ ⟹ Tr (mat_mult (sum_t m f P ) ρ) = Tr (mat_mult P (sum m f ρ ))"
apply (induct m,auto)
apply(simp add:mult_allo1)
apply(simp add:mult_allo2)
apply(simp add:tr_allo)
apply(simp add:b3)
done
primrec sum1::"(Mat*com*Mat) list⇒Mat"where
"sum1 []  =zero"|
"sum1  (a#M)  =  (mat_add (uu (fst a ) (snd (snd a)))  (sum1 M  ))  "
primrec sum4::"(Mat*com) list⇒Mat"where
"sum4 [] =zero"|
"sum4 (a#M)  =mat_add (mat_mult (dag (fst a) ) (fst a)) (sum4 M )"

primrec validlist :: "(Mat * com * Mat) list ⇒ Mat ⇒ bool" where
"validlist [] Q = True "
| "validlist (a # mcml) Q = ( (valid (snd (snd a)) (fst (snd a)) Q) ∧ (validlist  mcml Q) )"

lemma mea_ρ:"wellDefined (Cond M) ⟹∀ρ. positive ρ ⟶ Tr (mat_mult (sum1 M) ρ) ≤ Tr (mat_mult Q (denoFun (Cond M) ρ)) + Tr (mat_mult (M_sum M) ρ) - Tr (denoFun (Cond M) ρ)
⟹ ∀ρ. positive ρ  ⟶ Tr (mat_mult (sum1 M) ρ) ≤ Tr (mat_mult Q (denoFun (Cond M) ρ)) + Tr ρ - Tr (denoFun (Cond M) ρ)"
by (metis Ident wellDefined.simps(5))
lemma neq1:"(b::real)≤d⟹a≤c⟹(b+a)≤(d+c)"
apply auto
done
lemma mea1:"validlist M Q ⟹ ∀ρ. positive ρ ⟶
        Tr (mat_mult (sum1 M) ρ) ≤ Tr (mat_mult Q (denoFun (Cond M) ρ)) + Tr (mat_mult (M_sum M) ρ) - Tr (denoFun (Cond M) ρ)"
apply(induct M,auto)
apply (smt I_zero less4 rho_zero zero_mult_l zero_mult_r zero_tr)
apply(simp add:mult_allo1)
apply(simp add:tr_allo)
apply(simp add:mult_allo2)
apply(simp add:tr_allo)
apply(cut_tac b="Tr (mat_mult (sum1 M) ρ)" and d="Tr (mat_mult Q
                   (case M of [] ⇒ zero | mc # mcr ⇒ mat_add (denoFun (fst (snd mc)) (u (fst mc) ρ)) (denoFun (Cond mcr) ρ))) +
              Tr (mat_mult (M_sum M) ρ) -
              Tr (case M of [] ⇒ zero | mc # mcr ⇒ mat_add (denoFun (fst (snd mc)) (u (fst mc) ρ)) (denoFun (Cond mcr) ρ))"
and a=" Tr (mat_mult (uu a b) ρ)" and c=" Tr (mat_mult Q (denoFun aa (u a ρ)))+ (Tr (mat_mult (mat_mult (dag a) a) ρ))-Tr (denoFun aa (u a ρ))"
in neq1,auto)
apply(simp add:valid_def)
apply(subgoal_tac "positive ρ⟹positive (u a ρ)")
prefer 2
apply (metis rho)
apply(drule_tac x="(u a ρ)"in spec)
apply(drule_tac x="(u a ρ)"in spec,auto)
by (metis exchange mult_exchange u_def uu_def)
 (*   six rules         *)
 (*   Skip                   *)
lemma Skip:"valid P SKIP P"
apply (simp add:valid_def)
done
(*  Utrans       *)
lemma Utrans:"wellDefined (Utrans U n) ⟹valid  (mat_mult (mat_mult (dag U) P) U)  (Utrans U n) P"
apply(simp add:valid_def)  
apply(simp add:b3)
apply(simp add:exchange)
apply(simp add:b4)
apply(simp add:U_dag)
apply(simp add:Ident)
done
(*  Initial          *)
lemma Init:"wellDefined (Init m n) ⟹valid (sum_t (h m) f P)  (Init m n) P"
apply(simp add:valid_def, auto)
apply(simp add:m_init)
apply (simp add: Initfact)
done
(*   Sequence         *)
lemma Seq:"wellDefined (s1;s2) ⟹valid P s1 Q⟹valid Q s2 R⟹valid P (s1;s2) R"
apply(simp add:valid_def,auto)
apply(drule_tac x=" ρ" in spec)
apply(subgoal_tac " positive ρ⟹positive (denoFun s1 ρ)")
apply auto
apply (metis b)
done
(*     Measure          *)
lemma Measure:"wellDefined (Cond M) ⟹ validlist M Q ⟹ valid (sum1 M) (Cond M ) Q" 
unfolding valid_def
apply(rule mea_ρ)
apply(simp)
apply(rule mea1,auto)
done
lemma While_aux:" mat_add (mat_mult (dag m0) m0) (mat_mult (dag m1) m1) = I ∧ wellDefined S ⟹
   Matrix.less (mat_add (uu m0 P) (uu m1 Q)) I ⟹ Matrix.less P I ⟹
    ∀ρ. positive ρ ⟶ Tr (mat_mult (mat_sub I (mat_add (uu m0 P) (uu m1 Q))) (denoFun S ρ)) ≤ Tr (mat_mult (mat_sub I Q) ρ) ⟹
    ∀ρ. positive ρ ⟶
        Tr (mat_mult (mat_sub I P)  (while_n (denoFun S) m0 m1 ρ n))
        ≤ Tr (mat_mult (mat_sub I (mat_add (uu m0 P) (uu m1 Q))) ρ)"
 apply(induct n,auto)
 apply (simp add: less44 less_def zero_mult_l zero_mult_r zero_tr)
 apply(simp add:mult_allo2)
 apply(simp add:tr_allo)
 apply(drule_tac x="denoFun S (u m1 ρ)" in spec)
 apply(subgoal_tac " positive (denoFun S (u m1 ρ))")
 prefer 2
 using quantum_hoare_logic.b rho apply blast
apply(subgoal_tac " Tr (mat_mult (mat_sub I P) (u m0 ρ)) +  Tr (mat_mult (mat_sub I (mat_add (uu m0 P) (uu m1 Q))) (denoFun S (u m1 ρ)))
           ≤ Tr (mat_mult (mat_sub I (mat_add (uu m0 P) (uu m1 Q))) ρ) ")
apply simp
apply(subgoal_tac "positive (u m1 ρ)")
prefer 2
apply(simp add:rho)
apply(drule_tac x="u m1 ρ"in spec,auto)
apply(subgoal_tac " Tr (mat_mult (mat_sub I P) (u m0 ρ)) + Tr (mat_mult (mat_sub I Q) (u m1 ρ))
           ≤ Tr (mat_mult (mat_sub I (mat_add (uu m0 P) (uu m1 Q))) ρ)")
apply simp
apply(simp add:mult_sub_allo1)
apply(simp add:tr_allo1)
apply(simp add:Ident)
apply(subgoal_tac " Tr (u m0 ρ)+Tr (u m1 ρ) =(Tr ρ)")
prefer 2
apply(simp add:u_def)
apply(simp add:exchange_tr)
apply(subgoal_tac " Tr (mat_mult (mat_mult (dag m0)  m0) ρ) + Tr (mat_mult (mat_mult (dag m1)  m1) ρ) = Tr ρ")
apply (simp add: mult_exchange)
apply (metis Ident mult_allo1 tr_allo)
by (simp add: b3 mult_allo1 tr_allo u_def uu_def)
(*    while      *)
lemma While:"wellDefined (While m0 m1 S Q) ⟹ less (mat_add (uu m0 P) (uu m1 Q)) I⟹ less P I⟹
     svalid Q S (mat_add (uu m0 P) (uu m1 Q)) 
      ⟹valid (mat_add (uu m0 P) (uu m1 Q))  (While m0 m1 S Q ) P"
apply(rule eq_valid)
apply(simp add:svalid_def,auto)
prefer 2
apply (simp add: while_convergent)
apply(rule important_advance,auto)
apply (simp add: less_def)
apply (simp add: bb_aux quantum_hoare_logic.b)
apply(rule_tac x="Tr ρ"in exI)
apply (simp add: bb_aux5 quantum_hoare_logic.b)
apply (simp add: bb_aux2 quantum_hoare_logic.b)
by (simp add: While_aux)
(* order*)
lemma Order:"less P Pa⟹valid Pa S Q⟹valid P S Q"
apply(simp add:valid_def)
apply auto
apply(drule_tac x=" ρ" in spec)
apply auto
using less2 by fastforce
(*  about wlp *)
definition matsum::"nat ⇒nat⇒Mat⇒Mat" where
"matsum m n P=(sum_t (h m) f P)"
definition matUtrans::"Mat⇒nat⇒Mat⇒Mat" where
"matUtrans U n P=(mat_mult (mat_mult (dag U) P) U)"
 function wlp::"Mat⇒com⇒Mat"where
 "wlp P (SKIP) =P"|
 "wlp P (Init m n) =matsum m n P"|
 "wlp P (Utrans U n) =matUtrans U n P"|
 "wlp P ( Seq c1 c2) =wlp (wlp P c2) c1"|
 "wlp P (Cond mcl ) = (case mcl of [] ⇒ zero
  | mc # mcr ⇒ mat_add (uu (fst mc) (wlp P (fst (snd mc))))  (wlp P (Cond mcr)) ) " |
  "wlp P (While m0 m1 s Q) =zero"
by  pat_completeness auto 
termination 
 apply (relation "measure (λ(c,m).rank m)", auto )
 done
 (*wlp_init*)
lemma w_init:"positive ρ⟹wellDefined (Init m n) ⟹
∀Q. Tr (mat_mult (wlp Q (Init m n)) ρ) =Tr (mat_mult Q (denoFun (Init m n) ρ)) +Tr ρ-Tr (denoFun (Init m n) ρ)"
apply(simp add:matsum_def)
apply(simp add:m_init)
apply(simp add:Initfact)
done
(*wlp_utrans*)
lemma w_utrans:"positive ρ⟹wellDefined (Utrans U n) ⟹
∀Q. Tr (mat_mult (wlp Q (Utrans U n)) ρ) =Tr (mat_mult Q (denoFun (Utrans U n) ρ)) +Tr ρ-Tr (denoFun (Utrans U n) ρ)"
apply(simp add:matUtrans_def)
by (metis (no_types, hide_lams) Ident U_dag add.commute b3 diff_0 diff_add_cancel diff_diff_eq2 diff_minus_eq_add exchange minus_diff_eq mult_exchange mult_sub_allo1 tr_allo1 u_def uu_def)
(* wlp_seq *)
lemma w_seq:"positive ρ⟹wellDefined (Sa;Sb) ⟹
      ∀Q ρ. positive ρ ⟶ Tr (mat_mult (wlp Q Sa) ρ) = Tr (mat_mult Q (denoFun Sa ρ)) + Tr ρ - Tr (denoFun Sa ρ) ⟹
       ∀Q ρ. positive ρ ⟶ Tr (mat_mult (wlp Q Sb) ρ) = Tr (mat_mult Q (denoFun Sb ρ)) + Tr ρ - Tr (denoFun Sb ρ) ⟹
∀Q. Tr (mat_mult (wlp Q (Sa;Sb)) ρ) =Tr (mat_mult Q (denoFun (Sa;Sb) ρ)) +Tr ρ-Tr (denoFun (Sa;Sb) ρ)"
apply auto
apply(drule_tac x="Q"in spec)
apply(drule_tac x="Q"in spec)
apply(drule_tac x="ρ"in spec)
apply(subgoal_tac "positive (denoFun Sa ρ)")
prefer 2
apply (metis b)
apply(drule_tac x="(denoFun Sa ρ)"in spec,auto)
done
lemma wlp_cond3:" M_sum x = I ⟹  Tr (mat_mult (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (uu (fst mc) (wlp Q (fst (snd mc)))) (wlp Q (Cond mcr))) ρ)
             ≤ Tr (mat_mult Q
                     (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (denoFun (fst (snd mc)) (u (fst mc) ρ)) (denoFun (Cond mcr) ρ))) +
                Tr (mat_mult (M_sum x) ρ) -
                Tr (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (denoFun (fst (snd mc)) (u (fst mc) ρ)) (denoFun (Cond mcr) ρ)) ⟹
Tr (mat_mult (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (uu (fst mc) (wlp Q (fst (snd mc)))) (wlp Q (Cond mcr))) ρ)
    ≤ Tr (mat_mult Q (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (denoFun (fst (snd mc)) (u (fst mc) ρ)) (denoFun (Cond mcr) ρ))) + Tr ρ -
       Tr (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (denoFun (fst (snd mc)) (u (fst mc) ρ)) (denoFun (Cond mcr) ρ))"
  apply(simp add:Ident)
  done
  lemma wlp_cond4:" (∀ a aa b  Q ρ.
                 (a, aa, b) ∈ set x ⟶positive Q⟶less Q I⟶
                  positive ρ ⟶ Tr (mat_mult (wlp Q aa) ρ) ≤ Tr (mat_mult Q (denoFun aa ρ)) + Tr ρ - Tr (denoFun aa ρ)) ⟹
             positive Q⟹less Q I⟹
             ∀a aa b. (a, aa, b) ∈ set x ⟶ wellDefined aa ⟹
             positive ρ ⟹
             Tr (mat_mult (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (uu (fst mc) (wlp Q (fst (snd mc)))) (wlp Q (Cond mcr))) ρ)
             ≤ Tr (mat_mult Q
                     (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (denoFun (fst (snd mc)) (u (fst mc) ρ)) (denoFun (Cond mcr) ρ))) +
                Tr (mat_mult (M_sum x) ρ) -
                Tr (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (denoFun (fst (snd mc)) (u (fst mc) ρ)) (denoFun (Cond mcr) ρ))"
apply(induct x,auto)
apply (simp add: zero_mult_r)
apply(simp add:mult_allo1)
apply(simp add:tr_allo)
apply(simp add:mult_allo2)
apply(simp add:tr_allo)
apply(cut_tac b=" Tr (mat_mult (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (uu (fst mc) (wlp Q (fst (snd mc)))) (wlp Q (Cond mcr))) ρ)" and 
    d=" Tr (mat_mult Q (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (denoFun (fst (snd mc)) (u (fst mc) ρ)) (denoFun (Cond mcr) ρ))) +
     Tr (mat_mult (M_sum x) ρ) - Tr (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (denoFun (fst (snd mc)) (u (fst mc) ρ)) (denoFun (Cond mcr) ρ))" and
       a=" Tr (mat_mult (uu a (wlp Q aa)) ρ)" and c=" Tr (mat_mult Q (denoFun aa (u a ρ))) +Tr (mat_mult (mat_mult (dag a) a) ρ) -Tr (denoFun aa (u a ρ))" in neq1)
apply blast
apply auto
apply(drule_tac x="a"in spec,auto)
apply(drule_tac x="a"in spec,auto)
apply(drule_tac x="aa"in spec,auto)
apply(drule_tac x="aa"in spec)
apply(drule_tac x="b"in spec)
apply(drule_tac x="b"in spec)
apply(drule_tac x="Q"in spec)
apply(subgoal_tac "positive (u a ρ)")
prefer 2
using rho apply auto[1]
apply(drule_tac x="u a ρ"in spec,auto)
apply (metis (no_types, lifting) exchange_tr mult_exchange u_def uu_def)+
done

lemma wlp_cond2:" (∀ a aa b  Q ρ.
                 (a, aa, b) ∈ set x ⟶positive Q⟶less Q I⟶
                  positive ρ ⟶ Tr (mat_mult (wlp Q aa) ρ) ≤ Tr (mat_mult Q (denoFun aa ρ)) + Tr ρ - Tr (denoFun aa ρ)) ⟹
             positive Q⟹less Q I⟹ M_sum x = I ⟹
             ∀a aa b. (a, aa, b) ∈ set x ⟶ wellDefined aa ⟹
             positive ρ ⟹
             Tr (mat_mult (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (uu (fst mc) (wlp Q (fst (snd mc)))) (wlp Q (Cond mcr))) ρ)
             ≤ Tr (mat_mult Q
                     (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (denoFun (fst (snd mc)) (u (fst mc) ρ)) (denoFun (Cond mcr) ρ))) +
                Tr (mat_mult (M_sum x) ρ) -
                Tr (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (denoFun (fst (snd mc)) (u (fst mc) ρ)) (denoFun (Cond mcr) ρ))"
 apply(rule wlp_cond4,auto)
done
lemma wlp_cond1:" (∀ a aa b  Q ρ.
                 (a, aa, b) ∈ set x ⟶positive Q⟶less Q I⟶
                  positive ρ ⟶ Tr (mat_mult (wlp Q aa) ρ) ≤ Tr (mat_mult Q (denoFun aa ρ)) + Tr ρ - Tr (denoFun aa ρ)) ⟹
           positive Q⟹ less Q I⟹ M_sum x = I ⟹
             ∀a aa b. (a, aa, b) ∈ set x ⟶ wellDefined aa ⟹
             positive ρ ⟹
             Tr (mat_mult (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (uu (fst mc) (wlp Q (fst (snd mc)))) (wlp Q (Cond mcr))) ρ)
             ≤ Tr (mat_mult Q
                     (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (denoFun (fst (snd mc)) (u (fst mc) ρ)) (denoFun (Cond mcr) ρ))) +
                Tr ρ -
                Tr (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (denoFun (fst (snd mc)) (u (fst mc) ρ)) (denoFun (Cond mcr) ρ))"

 apply(rule wlp_cond3,auto)
using wlp_cond2 by auto
(* wlp_cond*)
lemma wlp_cond:" (∀ a aa b aaa ba xaaa Q ρ.
                 (a, aa, b) ∈ set x ⟶
                 (aaa, ba) ∈ Basic_BNFs.snds (a, aa, b) ⟶
                 xaaa ∈ Basic_BNFs.fsts (aaa, ba) ⟶positive Q⟶less Q I⟶
                  positive ρ ⟶ Tr (mat_mult (wlp Q xaaa) ρ) ≤ Tr (mat_mult Q (denoFun xaaa ρ)) + Tr ρ - Tr (denoFun xaaa ρ)) ⟹
            positive Q⟹ less Q I⟹
                  M_sum x = I ⟹
             ∀a aa b. (a, aa, b) ∈ set x ⟶
                      (∀aaa ba. (aaa, ba) ∈ Basic_BNFs.snds (a, aa, b) ⟶
                                (∀xaaa. xaaa ∈ Basic_BNFs.fsts (aaa, ba) ⟶ wellDefined xaaa)) ⟹
             positive ρ ⟹
             Tr (mat_mult (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (uu (fst mc) (wlp Q (fst (snd mc)))) (wlp Q (Cond mcr))) ρ)
             ≤ Tr (mat_mult Q
                     (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (denoFun (fst (snd mc)) (u (fst mc) ρ)) (denoFun (Cond mcr) ρ))) +
                Tr ρ -
                Tr (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (denoFun (fst (snd mc)) (u (fst mc) ρ)) (denoFun (Cond mcr) ρ))"

 apply(rule wlp_cond1,auto)
using fsts.intros snds.intros apply fastforce
using fsts.intros snds.intros by fastforce

lemma QI_aux2:"less Q I ⟹less (sum_t (h x1) f Q) (sum_2 (h x1) f)"
apply(induct x1,auto)
apply(subgoal_tac "less (mat_mult (mat_mult (dag (f (Suc x1))) Q) (f (Suc x1)))
                   (mat_mult (dag (f (Suc x1))) (f (Suc x1))) ")
apply(simp add:less6)
apply(subgoal_tac "less (mat_mult (mat_mult (dag (f (Suc x1))) Q) (f (Suc x1))) 
            (mat_mult   (mat_mult  (dag (f (Suc x1))) I)    (f (Suc x1)))")
apply (simp add: Ident_dual)
apply(rule less20,auto)
done
lemma QI_aux:" sum_1 (h x1) f = I ⟹ sum_2 (h x1) f = I ⟹ Matrix.less Q I ⟹ Matrix.less (sum_t (h x1) f Q) I"
apply(subgoal_tac "less (sum_t (h x1) f Q)  (sum_2 (h x1) f) ")
apply auto[1]
apply(rule QI_aux2,auto)
done
lemma QI_aux5:" (∀ a aa b Q . (a, aa, b) ∈ set x ⟶ Matrix.less Q I ⟶ Matrix.less (wlp Q aa) I) ⟹
           ∀a aa b. (a, aa, b) ∈ set x ⟶  wellDefined aa ⟹
           Matrix.less Q I ⟹
           Matrix.less (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (uu (fst mc) (wlp Q (fst (snd mc)))) (wlp Q (Cond mcr))) (M_sum x)"
        apply(induct x,auto)
       apply (simp add: less11)
       
       
       (*apply(drule_tac x="a" in spec)
       apply(drule_tac x="a" in spec)
       apply(drule_tac x="aa" in spec)
       apply(drule_tac x="aa" in spec)
       apply(drule_tac x="b" in spec)
       apply(drule_tac x="b" in spec)
       apply(drule_tac x="Q" in spec)*)
       apply(subgoal_tac "Matrix.less (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (uu (fst mc) (wlp Q (fst (snd mc)))) (wlp Q (Cond mcr))) (M_sum x)")
       apply(subgoal_tac "less (uu a (wlp Q aa))  (mat_mult (dag a) a)")
       apply(simp add:less6)
       apply(subgoal_tac " Matrix.less (uu a (wlp Q aa)) (mat_mult(mat_mult (dag a) I)  a)")
       apply (simp add: Ident_dual )
       apply(simp add:uu_def)
       apply(rule less20)
       apply simp
      by blast
lemma QI_aux4:" (∀ a aa b Q . (a, aa, b) ∈ set x ⟶ Matrix.less Q I ⟶ Matrix.less (wlp Q aa) I) ⟹
           M_sum x = I ⟹
           ∀a aa b. (a, aa, b) ∈ set x ⟶  wellDefined aa ⟹
           Matrix.less Q I ⟹
           Matrix.less (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (uu (fst mc) (wlp Q (fst (snd mc)))) (wlp Q (Cond mcr))) (M_sum x)"
        apply(rule QI_aux5,auto)
        done
lemma QI_aux3:" (∀ a aa b Q . (a, aa, b) ∈ set x ⟶ Matrix.less Q I ⟶ Matrix.less (wlp Q aa) I) ⟹
           M_sum x = I ⟹
           ∀a aa b. (a, aa, b) ∈ set x ⟶  wellDefined aa ⟹
           Matrix.less Q I ⟹
           Matrix.less (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (uu (fst mc) (wlp Q (fst (snd mc)))) (wlp Q (Cond mcr))) I"
using QI_aux4 by auto
lemma Q_I:"∀Q. wellDefined S⟶less Q I⟶less (wlp Q S) I"
apply(induct S,auto)
prefer 2
apply(simp add:matUtrans_def less_def)
apply (metis (full_types) Ident UMat_def dag_def less3_aux mult_exchange mult_sub_allo1 mult_sub_allo2 transpose_transpose_id)
apply(simp add:matsum_def )
apply(simp add:QI_aux)
prefer 2
apply (simp add: I_zero)
apply(rule QI_aux3,auto)
using fsts.intros snds.intros apply fastforce+
done
lemma temp_wlp:"positive P⟹positive (sum_t a f P)"
apply(induct a,auto)
by (metis c1 dag_dag less3_aux)
lemma temp_wlp1:" ((⋀a aa b. (a, aa, b) ∈ set x ⟹ ∀P. positive P ⟶ positive (wlp P aa)) ⟹
        positive (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (uu (fst mc) (wlp P (fst (snd mc)))) (wlp P (Cond mcr)))) ⟹
       (⋀aaa aaaa ba. aaa = a ∧ aaaa = aa ∧ ba = b ∨ (aaa, aaaa, ba) ∈ set x ⟹ ∀P. positive P ⟶ positive (wlp P aaaa)) ⟹
       positive P ⟹ positive
       (mat_add (uu a (wlp P aa)) (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (uu (fst mc) (wlp P (fst (snd mc)))) (wlp P (Cond mcr))))"
apply(subgoal_tac "positive (wlp P aa)")
prefer 2
apply blast
apply(subgoal_tac "positive (uu a (wlp P aa)) ")
prefer 2
apply(simp add:uu_def)
apply (metis dag_dag less3_aux)
using c1 by blast
lemma temp_wlp2:" (⋀a aa b.
               (a, aa, b) ∈ set x ⟹
               ∀P. positive P ⟶ positive (wlp P aa)) ⟹
           positive P ⟹ positive (case x of [] ⇒ zero | mc # mcr ⇒ mat_add (uu (fst mc) (wlp P (fst (snd mc)))) (wlp P (Cond mcr)))"
apply(induct x,auto)
using a1 less11 apply blast
apply( rule temp_wlp1,auto)
done
(*   positive (wlp p S)    *)
lemma posi_wlp:"∀P. positive P⟶positive (wlp P S)"
apply(induct S,auto)
apply(simp add:matsum_def temp_wlp)
apply (metis dag_dag less3_aux matUtrans_def)
prefer 2
apply (simp add: a1 less11)
apply(rule temp_wlp2,auto)
using fsts.intros snds.intros by fastforce

lemma aux111:" (∀ Q ρ. positive Q⟶Matrix.less Q I ⟶
               positive ρ ⟶ Tr (mat_mult (wlp Q S1) ρ) ≤ Tr (mat_mult Q (denoFun S1 ρ)) + Tr ρ - Tr (denoFun S1 ρ)) ⟹
       (∀ Q ρ .positive Q⟶ Matrix.less Q I ⟶
               positive ρ ⟶ Tr (mat_mult (wlp Q S2) ρ) ≤ Tr (mat_mult Q (denoFun S2 ρ)) + Tr ρ - Tr (denoFun S2 ρ)) ⟹
       positive Q⟹
       Matrix.less Q I ⟹
       positive ρ ⟹
       wellDefined S1 ⟹
       wellDefined S2 ⟹
       Tr (mat_mult (wlp (wlp Q S2) S1) ρ) ≤ Tr (mat_mult Q (denoFun S2 (denoFun S1 ρ))) + Tr ρ - Tr (denoFun S2 (denoFun S1 ρ))"
       apply auto
       apply(subgoal_tac "less (wlp Q S2) I")
       apply(subgoal_tac "positive (wlp Q S2)")
       apply(drule_tac x="wlp Q S2"in spec,auto)
       apply(drule_tac x="Q"in spec,auto)
      apply(drule_tac x="ρ"in spec,auto)
apply(subgoal_tac "positive (denoFun S1 ρ)")
prefer 2
apply (metis b)
apply(drule_tac x="(denoFun S1 ρ)"in spec,auto)
prefer 2
apply(simp add:Q_I)
apply(simp add:posi_wlp)
done
(*  Tr [s]ρ ≤Tr  ρ  *)
lemma less_deno:"wellDefined s⟹∀ρ. positive ρ⟶Tr (denoFun s ρ)≤Tr  ρ"
using bb_aux4 by blast
lemma while_aux:"  ∀ρ. positive ρ ⟶
       mat_add (mat_mult (dag x1) x1) (mat_mult (dag x2) x2) = I ⟶
       wellDefined S ⟶positive Q⟶
      Tr (mat_mult (mat_sub I Q) (while_n (denoFun S) x1 x2 ρ n)) ≤ Tr ρ"
     apply(simp add:mult_sub_allo1)
     apply(simp add:tr_allo1 Ident)
     apply(subgoal_tac "∀ρ. positive ρ ⟶
        mat_add (mat_mult (dag x1) x1) (mat_mult (dag x2) x2) = I ⟶positive Q⟶
        wellDefined S ⟶0 ≤ Tr (mat_mult Q (while_n (denoFun S) x1 x2 ρ n)) + Tr ρ -Tr (while_n (denoFun S) x1 x2 ρ n) ")
    apply auto[1]
    apply(induct n,auto)
    apply (simp add: positive_Tr zero_mult_r zero_tr)
    apply(simp add:tr_allo)
    apply(simp add:mult_allo2)
   apply(simp add:tr_allo)
    apply(subgoal_tac "positive (denoFun S (u x2 ρ))")
    prefer 2
    apply (simp add: quantum_hoare_logic.b rho)
    apply(drule_tac  x=" (denoFun S (u x2 ρ))" in spec,auto)
    apply(subgoal_tac " Tr (while_n (denoFun S) x1 x2 (denoFun S (u x2 ρ)) n)- Tr (mat_mult Q (while_n (denoFun S) x1 x2 (denoFun S (u x2 ρ)) n))
              ≤ Tr (mat_mult Q (u x1 ρ))  + Tr ρ - Tr (u x1 ρ)  ")
    apply linarith
    apply(subgoal_tac " Tr (while_n (denoFun S) x1 x2 (denoFun S (u x2 ρ)) n)- Tr (mat_mult Q (while_n (denoFun S) x1 x2 (denoFun S (u x2 ρ)) n))
              ≤ Tr (denoFun S (u x2 ρ))  ")
    apply simp
    apply(subgoal_tac " Tr (mat_mult Q (u x1 ρ)) +Tr ρ-Tr (u x1 ρ)-Tr (denoFun S (u x2 ρ)) ≥0")
    apply auto
    apply(subgoal_tac "positive (u x2 ρ)")
    prefer 2
    apply (simp add: rho)
    apply(subgoal_tac "Tr (denoFun S (u x2 ρ))≤Tr (u x2 ρ)")
    prefer 2
    apply(simp add:less_deno)
    apply(subgoal_tac " Tr (denoFun S (u x2 ρ)) ≤Tr (u x2 ρ)")
    prefer 2
    apply (simp add: bb_aux4)
    apply(subgoal_tac " 0 ≤ Tr (mat_mult Q (u x1 ρ)) + Tr ρ - Tr (u x1 ρ) - Tr  (u x2 ρ)")
    apply simp
     apply(simp add:u_def)
      apply(simp add:exchange )
      apply(subgoal_tac " Tr (mat_mult (dag x1) (mat_mult x1 ρ)) +
                Tr (mat_mult (dag x2) (mat_mult x2 ρ)) =Tr ρ")
      prefer 2
      apply(subgoal_tac " Tr (mat_mult (dag x1) (mat_mult x1 ρ)) + Tr (mat_mult (dag x2) (mat_mult x2 ρ)) =
           Tr (mat_add (mat_mult (dag x1) (mat_mult x1 ρ)) (mat_mult (dag x2) (mat_mult x2 ρ))) ")
      prefer 2
      apply(simp add:tr_allo,simp)
      apply (metis Ident b4 mult_allo1)
      apply(subgoal_tac " 0 ≤ Tr (mat_mult Q (mat_mult (mat_mult x1 ρ) (dag x1)))")
      apply simp
     using less3_aux less44 by blast
     

lemma soundwp1: "wellDefined S ⟹∀ Q. positive Q⟶ less Q I⟶ valid (wlp Q S) S  Q"
apply(simp add:valid_def,auto)
apply(induct S,auto)
apply (simp add: Initfact m_init matsum_def)
using Ident UMat_def b3 b4 exchange_tr matUtrans_def apply auto[1]
apply (simp add: aux111)
apply(rule wlp_cond,auto)
prefer 2
apply (simp add: while_convergent)
apply(subgoal_tac " Tr (mat_mult zero ρ) =0",auto)
prefer 2
apply (simp add: zero_mult_l zero_tr)
apply(subgoal_tac "Tr (mat_mult (mat_sub I Q) (Abs_matrix (λi j. lim (λn. Rep_matrix (while_n (denoFun S) x1 x2 ρ n) i j)))) ≤ Tr ρ")
apply (simp add: Ident mult_sub_allo1 tr_allo1)
apply(rule important_advance,auto)
apply (simp add: less_def)
apply (simp add: bb_aux quantum_hoare_logic.b)
apply(rule_tac x="Tr ρ"in exI)
apply (simp add: bb_aux5 quantum_hoare_logic.b)
apply (simp add: bb_aux2 quantum_hoare_logic.b)
apply(simp add:while_aux)
done

lemma WLPsound:"positive Q⟹less Q I⟹wellDefined S⟹valid (wlp Q S) S Q"
apply(simp add: soundwp1)
done
lemma ord_wlp:"less Q I⟹positive Q⟹less P I⟹wellDefined S⟹less P (wlp Q S)⟹valid P S Q"
apply(rule_tac Pa="wlp Q S" in Order,auto)
apply(rule WLPsound)
apply auto
done
lemma ord_wlp1:"less Q I⟹positive Q⟹less P I⟹wellDefined S⟹less P (wlp Q S)⟹svalid P S Q"
by (simp add: eq_valid2 ord_wlp)
declare uu_def[simp]
ML_file "Quantum_Hoare_tac.ML"
method_setup vcg = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (quantum_hoare_tac ctxt (K all_tac))) *}
method_setup vcg_simp = {*
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD' (quantum_hoare_tac ctxt (asm_full_simp_tac ctxt))) *}
end
