theory examples
imports Main   "quantum_hoare_logic" "lt"
begin
(*
lemma grover:  "valid I  
               (((Init 2 0;Init 2 1;Init 2 2;Init 4 3;
               Utrans Delta 2;Utrans H 0;Utrans H 1;Utrans H 2);
              While M0 M1 (Utrans Or (10);Utrans H 0;Utrans H 1;Utrans Ph 10;
         Utrans H 0; Utrans H 1) Q);
           Cond [(N0,SKIP,P),(N1,SKIP,P),(N2,SKIP,P),(N3,SKIP,P)] )             
               P"
apply(rule_tac Q="wlp P (Cond [(N0,SKIP,P),(N1,SKIP,P),(N2,SKIP,P),(N3,SKIP,P)]) " in Seq)
prefer 2
apply(rule_tac Q="mat_add (uu M0 (wlp P (Cond [(N0, SKIP, P), (N1, SKIP, P), (N2, SKIP, P), (N3, SKIP, P)]))) (uu M1 Q)"in Seq)
prefer 2
apply simp
apply vcg     
prefer 5
apply simp
apply quantum_oracle
prefer 6
apply(rule While)
prefer 4
apply(rule ord_wlp1,auto)
apply quantum_oracle+
apply (metis fst_eqD fsts.cases snd_eqD snds.cases wellDefined.simps(1))+
apply vcg
prefer 5
apply(simp add:zero_add)
apply quantum_oracle+
done*)
(*
lemma shor:"valid P  (Init 2 0;Utrans H 0;Utrans U 1;Utrans (dag U) 1;Utrans (dag H) 0;
                    Cond [(M0,SKIP,Q),(M1,SKIP,Q)])   Q"
apply(rule ord_wlp,auto)
apply quantum_oracle+
apply (metis fst_conv fsts.cases snd_conv snds.cases wellDefined.simps(1))
apply (metis fst_conv fsts.cases snd_conv snds.cases wellDefined.simps(1))
apply quantum_oracle
done*)
end
