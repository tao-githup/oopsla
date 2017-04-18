theory convergent
imports Main Limits Matrix
begin
lemma test :"∀e>0. ∃M. ∀m≥M. ∀n≥M. n>m⟶ dist ((X::nat⇒real) m) (X n) < e⟹∀e>0. ∃M. ∀m≥M. ∀n≥M. n<m⟶ dist (X m) (X n) < e⟹
∀e>0. ∃M. ∀m≥M. ∀n≥M. n=m⟶ dist (X m) (X n) < e⟹
         ∀e>0. ∃M. ∀m≥M. ∀n≥M. dist (X m) (X n) < e"
apply auto
apply(drule_tac x="e"in spec ,auto)
apply(drule_tac x="e"in spec ,auto)
apply(rule_tac x="max M Ma"in exI,auto)
apply(drule_tac x="m"in spec,auto )
apply(drule_tac x="m"in spec ,auto)
apply(drule_tac x="n"in spec ,auto)
done
lemma Cauchy_conv:"(∀e>0. ∃M. ∀n ≥ M. ∀m ≥ n. dist ((X::nat⇒real) m) (X n) < e) ⟹Cauchy X"
apply (simp add:Cauchy_def)
apply(rule test,auto)
apply(drule_tac x="e"in spec ,auto)
apply(rule_tac x="M"in exI,auto)
apply (simp add: dist_commute)
by (metis (full_types) dist_commute nat_less_le)
lemma Cauchy_conv_dual:"Cauchy X⟹(∀e>0. ∃M. ∀n ≥ M. ∀m ≥ n. dist ((X::nat⇒real) m) (X n) < e) "
apply (simp add:Cauchy_def)
apply auto
apply(drule_tac x="e"in spec ,auto)
apply(rule_tac x="M"in exI,auto)
done
lemma convergent_aux:" ∀e>0. ∃M. ∀n≥M. ∀m≥n. (dist  ((A m)::real)  (A n))*((dist  ((A m)::real)  (A n))) < e
                   ⟹∀e>0. ∃M. ∀n≥M. ∀m≥n. dist (A m) (A n) < e"
       apply(auto)
       apply(drule_tac x="e*e" in spec,auto)
       apply(rule_tac x="M" in exI)
       by (metis (full_types) less_eq_real_def mult_le_less_imp_less not_less)
lemma convergent_aux5:" 0 ≤ foldseq_transposed op + (λka. (Rep_matrix (A m) 0 ka - Rep_matrix (A n) 0 ka) * (Rep_matrix (A m) 0 ka - Rep_matrix (A n) 0 ka))
          N"
          apply(induct N,auto)
          done
lemma convergent_aux6:"foldseq_transposed op +
               (λka. (Rep_matrix (A m) (Suc N) ka - Rep_matrix (A n) (Suc N) ka) *
                     (Rep_matrix (A m) (Suc N) ka - Rep_matrix (A n) (Suc N) ka)) M≥0"
         apply(induct M,auto)
         done
lemma convergent_aux4:"0 ≤ foldseq_transposed op +
          (λk. foldseq_transposed op + (λka. (Rep_matrix (A m) k ka - Rep_matrix (A n) k ka) * (Rep_matrix (A m) k ka - Rep_matrix (A n) k ka))
                infinite)  N"
      apply(induct N,auto)
      apply(simp add:convergent_aux5)
      apply(simp add:convergent_aux6)
      done

lemma convergent_aux7:"i≥infinite∨j≥infinite⟶(Rep_matrix (A m) i j - Rep_matrix (A n) i j) * (Rep_matrix (A m) i j - Rep_matrix (A n) i j)
    ≤ foldseq op + (λk. foldseq op + (λka. Rep_matrix (mat_sub (A m) (A n)) k ka * Rep_matrix (mat_sub (A m) (A n)) k ka) infinite)
        infinite⟹i<infinite∧j<infinite⟶ (Rep_matrix (A m) i j - Rep_matrix (A n) i j) * (Rep_matrix (A m) i j - Rep_matrix (A n) i j)
    ≤ foldseq op + (λk. foldseq op + (λka. Rep_matrix (mat_sub (A m) (A n)) k ka * Rep_matrix (mat_sub (A m) (A n)) k ka) infinite)
        infinite⟹ (Rep_matrix (A m) i j - Rep_matrix (A n) i j) * (Rep_matrix (A m) i j - Rep_matrix (A n) i j)
    ≤ foldseq op + (λk. foldseq op + (λka. Rep_matrix (mat_sub (A m) (A n)) k ka * Rep_matrix (mat_sub (A m) (A n)) k ka) infinite)
        infinite"
using not_less by blast
lemma foldseq_aux:"∀n. (ff::nat⇒real) n≥0⟹foldseq_transposed op+ ff m≤foldseq_transposed op+ ff (m+a::nat)"
apply(induct a,auto)
apply(drule_tac x="Suc (m+a)" in spec,auto)
done
lemma foldseq_aux1:"∀n. (ff::nat⇒real) n≥0⟹m≤n⟹foldseq_transposed op+ ff m≤foldseq_transposed op+ ff n"
      using foldseq_aux le_Suc_ex by blast
lemma foldseq_aux2:"∀n. (ff::nat⇒real) n≥0⟹ff n≤foldseq_transposed op+ ff n"
apply(induct n,auto)
using dual_order.trans by blast
lemma convergent_aux9:" i < N ⟹ j < N ⟹
    (Rep_matrix (A m) i j - Rep_matrix (A n) i j) * (Rep_matrix (A m) i j - Rep_matrix (A n) i j)
    ≤ foldseq op + (λk. foldseq op + (λka. Rep_matrix (mat_sub (A m) (A n)) k ka * Rep_matrix (mat_sub (A m) (A n)) k ka) N) N"
     apply (simp add: associative_def foldseq_assoc)
     apply(subgoal_tac "(Rep_matrix (A m) i j - Rep_matrix (A n) i j) * (Rep_matrix (A m) i j - Rep_matrix (A n) i j)
    ≤ foldseq_transposed op +
        (λk. foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) k ka * Rep_matrix (mat_sub (A m) (A n)) k ka) N) i")
     apply(subgoal_tac "( foldseq_transposed op +
        (λk. foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) k ka * Rep_matrix (mat_sub (A m) (A n)) k ka) N) i)≤
         foldseq_transposed op +
        (λk. foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) k ka * Rep_matrix (mat_sub (A m) (A n)) k ka) N) N")
     prefer 2
     apply(rule foldseq_aux1,auto)
     using aux5 apply auto[1]
     apply(subgoal_tac "  foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) i ka * Rep_matrix (mat_sub (A m) (A n)) i ka) N
          ≤ foldseq_transposed op +
        (λk. foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) k ka * Rep_matrix (mat_sub (A m) (A n)) k ka) N) i")
     prefer 2
     apply(rule foldseq_aux2,auto)
     using aux5 apply auto[1]
     apply(subgoal_tac "(Rep_matrix (A m) i j - Rep_matrix (A n) i j) * (Rep_matrix (A m) i j - Rep_matrix (A n) i j)
            ≤ foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) i ka * Rep_matrix (mat_sub (A m) (A n)) i ka) N")
     apply auto
     apply(subgoal_tac " foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) i ka * Rep_matrix (mat_sub (A m) (A n)) i ka) j≤
        foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) i ka * Rep_matrix (mat_sub (A m) (A n)) i ka) N")
     prefer 2
     apply(rule foldseq_aux1,auto)
     apply(subgoal_tac" (Rep_matrix (A m) i j - Rep_matrix (A n) i j) * (Rep_matrix (A m) i j - Rep_matrix (A n) i j)
    ≤ foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) i ka * Rep_matrix (mat_sub (A m) (A n)) i ka) j")
     apply auto
     apply(subgoal_tac " Rep_matrix (mat_sub (A m) (A n)) i j * Rep_matrix (mat_sub (A m) (A n)) i j  ≤
       foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) i ka * Rep_matrix (mat_sub (A m) (A n)) i ka) j ")
     prefer 2
      apply(rule foldseq_aux2,auto)
     apply(subgoal_tac "(Rep_matrix (A m) i j - Rep_matrix (A n) i j) * (Rep_matrix (A m) i j - Rep_matrix (A n) i j) =
        Rep_matrix (mat_sub (A m) (A n)) i j * Rep_matrix (mat_sub (A m) (A n)) i j",auto)
     apply(simp add:mat_sub_def)
     apply(simp add:diff_matrix_def)
     done
lemma convergent_aux9_1:" i < N ⟹ j < N ⟹
    (Rep_matrix (A m) i j - Rep_matrix (A n) i j) * (Rep_matrix (A m) i j - Rep_matrix (A n) i j)
    ≤ foldseq op + (λk. foldseq op + (λka. Rep_matrix (mat_sub (A m) (A n)) k ka * Rep_matrix (mat_sub (A m) (A n)) k ka) N) N"
     apply (simp add: associative_def foldseq_assoc)
     apply(subgoal_tac "(Rep_matrix (A m) i j - Rep_matrix (A n) i j) * (Rep_matrix (A m) i j - Rep_matrix (A n) i j)
    ≤ foldseq_transposed op +
        (λk. foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) k ka * Rep_matrix (mat_sub (A m) (A n)) k ka) N) i")
     apply(subgoal_tac "( foldseq_transposed op +
        (λk. foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) k ka * Rep_matrix (mat_sub (A m) (A n)) k ka) N) i)≤
         foldseq_transposed op +
        (λk. foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) k ka * Rep_matrix (mat_sub (A m) (A n)) k ka) N) N")
     prefer 2
     apply(rule foldseq_aux1,auto)
     using aux5 apply auto[1]
     apply(subgoal_tac "  foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) i ka * Rep_matrix (mat_sub (A m) (A n)) i ka) N
          ≤ foldseq_transposed op +
        (λk. foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) k ka * Rep_matrix (mat_sub (A m) (A n)) k ka) N) i")
     prefer 2
     apply(rule foldseq_aux2,auto)
     using aux5 apply auto[1]
     apply(subgoal_tac "(Rep_matrix (A m) i j - Rep_matrix (A n) i j) * (Rep_matrix (A m) i j - Rep_matrix (A n) i j)
            ≤ foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) i ka * Rep_matrix (mat_sub (A m) (A n)) i ka) N")
     apply auto
     apply(subgoal_tac " foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) i ka * Rep_matrix (mat_sub (A m) (A n)) i ka) j≤
        foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) i ka * Rep_matrix (mat_sub (A m) (A n)) i ka) N")
     prefer 2
     apply(rule foldseq_aux1,auto)
     apply(subgoal_tac" (Rep_matrix (A m) i j - Rep_matrix (A n) i j) * (Rep_matrix (A m) i j - Rep_matrix (A n) i j)
    ≤ foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) i ka * Rep_matrix (mat_sub (A m) (A n)) i ka) j")
     apply auto
     apply(subgoal_tac " Rep_matrix (mat_sub (A m) (A n)) i j * Rep_matrix (mat_sub (A m) (A n)) i j  ≤
       foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) i ka * Rep_matrix (mat_sub (A m) (A n)) i ka) j ")
     prefer 2
      apply(rule foldseq_aux2,auto)
     apply(subgoal_tac "(Rep_matrix (A m) i j - Rep_matrix (A n) i j) * (Rep_matrix (A m) i j - Rep_matrix (A n) i j) =
        Rep_matrix (mat_sub (A m) (A n)) i j * Rep_matrix (mat_sub (A m) (A n)) i j",auto)
     apply(simp add:mat_sub_def)
     apply(simp add:diff_matrix_def)
     done
     
lemma convergent_aux3:" (Rep_matrix (A m) i j - Rep_matrix (A n) i j) * (Rep_matrix (A m) i j - Rep_matrix (A n) i j)
    ≤ foldseq op + (λk. foldseq op + (λka. Rep_matrix (mat_sub (A m) (A n)) k ka * Rep_matrix (mat_sub (A m) (A n)) k ka) infinite)
        infinite"
       apply(rule convergent_aux7 )
       apply(simp add: mat_sub_def diff_matrix_def)
       apply(rule conjI)
       apply auto[1]
       apply(subgoal_tac "Rep_matrix (A m) i j =0",simp)
       apply(subgoal_tac "Rep_matrix (A n) i j =0",simp)
       apply (simp add: associative_def foldseq_assoc)
       apply(simp add:convergent_aux4)
       apply (metis (mono_tags, hide_lams) ncols_max ncols_transpose nrows_le)+
       apply auto[1]
       apply(subgoal_tac "Rep_matrix (A m) i j =0",simp)
       apply(subgoal_tac "Rep_matrix (A n) i j =0",simp)
       apply (simp add: associative_def foldseq_assoc)
       apply(simp add:convergent_aux4)
       apply (metis (mono_tags, hide_lams) ncols_le nrows_max nrows_transpose)+
       apply (subgoal_tac "i < infinite ⟹ j < infinite ⟹
    (Rep_matrix (A m) i j - Rep_matrix (A n) i j) * (Rep_matrix (A m) i j - Rep_matrix (A n) i j)
    ≤ foldseq op + (λk. foldseq op + (λka. Rep_matrix (mat_sub (A m) (A n)) k ka * Rep_matrix (mat_sub (A m) (A n)) k ka) infinite)
        infinite ")
       apply blast
       apply(rule convergent_aux9)
       apply blast+
       done
lemma convergent_aux2:" all_sum_pow (mat_sub (A m) (A n)) ≥ (Rep_matrix (A m) i j - Rep_matrix (A n) i j) * (Rep_matrix (A m) i j - Rep_matrix (A n) i j) "
      apply(simp add:all_sum_pow_def) 
      apply(simp add:rows_sum_pow_def)
      apply(subgoal_tac " foldseq op +
        (λk. foldseq op + (λka. Rep_matrix (mat_sub (A m) (A n)) k ka * Rep_matrix (mat_sub (A m) (A n)) k ka)
              (ncols (mat_sub (A m) (A n))))
        (nrows (mat_sub (A m) (A n))) = foldseq op +
        (λk. foldseq op + (λka. Rep_matrix (mat_sub (A m) (A n)) k ka * Rep_matrix (mat_sub (A m) (A n)) k ka)
              (ncols (mat_sub (A m) (A n))))
       infinite",auto)
      prefer 2
      apply(rule foldseq_zerotail,auto)
      apply (simp add: foldseq_zero nrows)
      apply(subgoal_tac " (λk. foldseq op + (λka. Rep_matrix (mat_sub (A m) (A n)) k ka * Rep_matrix (mat_sub (A m) (A n)) k ka)
              (ncols (mat_sub (A m) (A n)))) = (λk. foldseq op + (λka. Rep_matrix (mat_sub (A m) (A n)) k ka * Rep_matrix (mat_sub (A m) (A n)) k ka)
               infinite)",auto)
      prefer 2
      apply(rule ext)
      apply(rule foldseq_zerotail,auto)
      using ncols apply blast
      apply(simp add:convergent_aux3)
      done
lemma convergent_aux1:" ∀e>0. ∃M. ∀n≥M. ∀m≥n. all_sum_pow (mat_sub (A m) (A n)) < e
      ⟹ ∀e>0. ∃M. ∀n≥M. ∀m≥n. (Rep_matrix (A m) i j - Rep_matrix (A n) i j) * (Rep_matrix (A m) i j - Rep_matrix (A n) i j) < e"
     apply(auto)
     apply(drule_tac x="e" in spec,auto)
     apply(rule_tac x="M" in exI,auto)
     apply(drule_tac x="n"in spec ,auto)
     apply(drule_tac x="m"in spec ,auto)
     apply(subgoal_tac " all_sum_pow (mat_sub (A m) (A n)) ≥ (Rep_matrix (A m) i j - Rep_matrix (A n) i j) * (Rep_matrix (A m) i j - Rep_matrix (A n) i j)")
     apply auto
     apply(simp add:convergent_aux2)
     done
lemma convergent_aux15:" i < N ⟹ j < N ⟹
    (Rep_matrix (A m) i j - Rep_matrix (A n) i j) * (Rep_matrix (A m) i j - Rep_matrix (A n) i j)
    ≤ foldseq op + (λk. foldseq op + (λka. Rep_matrix (mat_sub (A m) (A n)) k ka * Rep_matrix (mat_sub (A m) (A n)) k ka) N) N"
     apply (simp add: associative_def foldseq_assoc)
     apply(subgoal_tac "(Rep_matrix (A m) i j - Rep_matrix (A n) i j) * (Rep_matrix (A m) i j - Rep_matrix (A n) i j)
    ≤ foldseq_transposed op +
        (λk. foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) k ka * Rep_matrix (mat_sub (A m) (A n)) k ka) N) i")
     apply(subgoal_tac "( foldseq_transposed op +
        (λk. foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) k ka * Rep_matrix (mat_sub (A m) (A n)) k ka) N) i)≤
         foldseq_transposed op +
        (λk. foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) k ka * Rep_matrix (mat_sub (A m) (A n)) k ka) N) N")
     prefer 2
     apply(rule foldseq_aux1,auto)
     using aux5 apply auto[1]
     apply(subgoal_tac "  foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) i ka * Rep_matrix (mat_sub (A m) (A n)) i ka) N
          ≤ foldseq_transposed op +
        (λk. foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) k ka * Rep_matrix (mat_sub (A m) (A n)) k ka) N) i")
     prefer 2
     apply(rule foldseq_aux2,auto)
     using aux5 apply auto[1]
     apply(subgoal_tac "(Rep_matrix (A m) i j - Rep_matrix (A n) i j) * (Rep_matrix (A m) i j - Rep_matrix (A n) i j)
            ≤ foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) i ka * Rep_matrix (mat_sub (A m) (A n)) i ka) N")
     apply auto
     apply(subgoal_tac " foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) i ka * Rep_matrix (mat_sub (A m) (A n)) i ka) j≤
        foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) i ka * Rep_matrix (mat_sub (A m) (A n)) i ka) N")
     prefer 2
     apply(rule foldseq_aux1,auto)
     apply(subgoal_tac" (Rep_matrix (A m) i j - Rep_matrix (A n) i j) * (Rep_matrix (A m) i j - Rep_matrix (A n) i j)
    ≤ foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) i ka * Rep_matrix (mat_sub (A m) (A n)) i ka) j")
     apply auto
     apply(subgoal_tac " Rep_matrix (mat_sub (A m) (A n)) i j * Rep_matrix (mat_sub (A m) (A n)) i j  ≤
       foldseq_transposed op + (λka. Rep_matrix (mat_sub (A m) (A n)) i ka * Rep_matrix (mat_sub (A m) (A n)) i ka) j ")
     prefer 2
      apply(rule foldseq_aux2,auto)
     apply(subgoal_tac "(Rep_matrix (A m) i j - Rep_matrix (A n) i j) * (Rep_matrix (A m) i j - Rep_matrix (A n) i j) =
        Rep_matrix (mat_sub (A m) (A n)) i j * Rep_matrix (mat_sub (A m) (A n)) i j",auto)
     apply(simp add:mat_sub_def)
     apply(simp add:diff_matrix_def)
     done
lemma fuck1:" ∀n. less (A n) (A (Suc n)) ⟹ Matrix.less (A m) (A (m + (a::nat)))"
apply (induct a,auto)
apply (simp add: less11)
apply(drule_tac x="m+a"in spec)
using transitivity by blast
lemma fuck:" ∀n. less (A n) (A (Suc n)) ⟹ n≥m⟹less (A m) (A n)"
by (metis add_Suc_right fuck1 le_less less11 less_imp_Suc_add)
lemma convergent_aux11:"∀n m. n≥m⟶less ((A::nat⇒matrix) m) (A n) ⟹∀ea>0. ∃M. ∀n≥M. ∀m≥n. (Tr (mat_sub (A m) (A n)))*(Tr (mat_sub (A m) (A n))) < ea⟹
            ∀ea>0. ∃M. ∀n≥M. ∀m≥n. Tr (mat_mult (mat_sub (A m) (A n)) (dag (mat_sub (A m) (A n)))) < ea"
            apply auto
            apply(drule_tac x="ea" in spec,auto)
            apply(rule_tac x="M" in exI,auto)
            apply(drule_tac x="n" in spec,auto)
            apply(drule_tac x="m" in spec,auto)
            apply(subgoal_tac " Tr (mat_mult (mat_sub (A m) (A n)) (dag (mat_sub (A m) (A n)))) ≤
              Tr (mat_sub (A m) (A n)) * Tr (mat_sub (A m) (A n))",auto)
            apply(rule advance)
            by (simp add: less_def)
lemma convergent_aux12_aux:"a≥0⟹a<sqrt e⟹a*a<e"
         using real_sqrt_less_iff by fastforce
lemma convergent_aux12:"∀n m. n≥m⟶less ((A::nat⇒matrix) m) (A n) ⟹ ∀eaa>0. ∃M. ∀n≥M. ∀m≥n. Tr (mat_sub (A m) (A n)) < eaa⟹
                     ∀eaa>0. ∃M. ∀n≥M. ∀m≥n. Tr (mat_sub (A m) (A n)) * Tr (mat_sub (A m) (A n)) < eaa"
          apply auto
          apply(drule_tac x="sqrt eaa" in spec,auto)
          apply(rule_tac x="M" in exI,auto)
          apply(drule_tac x="n" in spec,auto)
          apply(drule_tac x="m" in spec,auto)
          apply(subgoal_tac "Tr (mat_sub (A m) (A n)) ≥0")
          apply(rule convergent_aux12_aux)
          apply auto
          by (simp add: less_def positive_Tr)

lemma convergent:"  ∀n. positive (A n) ⟹ ∃B.∀n. Tr (A n) ≤B ⟹ ∀n. less (A n) (A (Suc n))
                       ⟹∀i j. convergent (λn. Rep_matrix (A n) i j)"
       apply(auto)
       apply(subgoal_tac " Cauchy (λn. Rep_matrix (A n) i j) ")
       apply (simp add: real_Cauchy_convergent)
       apply(rule Cauchy_conv)
       apply(rule convergent_aux,auto)
       apply(simp add:dist_real_def)
       apply(subgoal_tac " ∀e>0. ∃M. ∀n≥M. ∀m≥n. all_sum_pow (mat_sub (A m) (A n)) < e")
       apply (simp add: convergent_aux1,auto)
       apply(subgoal_tac "∃M. ∀n≥M. ∀m≥n. Tr (mat_mult (mat_sub (A m) (A n)) (dag (mat_sub (A m) (A n)))) < ea")
       apply(simp add:tr_pow)
       apply(cut_tac A="A" in convergent_aux11,auto)
       apply(simp add:fuck)
       apply(cut_tac A="A" in convergent_aux12,auto)
        apply(simp add:fuck)
        apply(simp add:tr_allo1)
        apply(subgoal_tac "Cauchy (λn. Tr (A n))")
        apply(subgoal_tac " ∀ee>0. ∃M. ∀n≥M. ∀m≥n. dist (Tr (A m)) (Tr (A n))<ee",auto)
        prefer 2
        apply(simp add: Cauchy_conv_dual)
        apply(simp add:dist_real_def)
        apply(drule_tac x="eaaa" in spec,auto)
        apply(rule_tac x="M" in exI,auto)
        apply(subgoal_tac "less (A n) (A m)")
        prefer 2
        using fuck apply blast
        apply(drule_tac x="n" in spec,auto)
        apply(subgoal_tac "convergent (λn. Tr (A n))")
        using Cauchy_convergent_iff apply blast
        apply(subgoal_tac "(λn. Tr (A n))---->(SUP i. Tr (A i)) ")
       using convergent_def apply blast
        apply(rule LIMSEQ_incseq_SUP)
        apply(simp add:bdd_above_def)
       apply(rule_tac x="B" in exI,auto)
       apply(simp add:incseq_def,auto)
       apply(subgoal_tac "less (A m) (A n)")
       apply(simp add:less_tr)
       apply(simp  add:fuck)
       done

end
