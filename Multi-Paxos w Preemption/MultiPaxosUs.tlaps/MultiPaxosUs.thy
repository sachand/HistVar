(* automatically generated -- do not edit manually *)
theory MultiPaxosUs imports Constant Zenon begin
ML_command {* writeln ("*** TLAPS PARSED\n"); *}
consts
  "isReal" :: c
  "isa_slas_a" :: "[c,c] => c"
  "isa_bksl_diva" :: "[c,c] => c"
  "isa_perc_a" :: "[c,c] => c"
  "isa_peri_peri_a" :: "[c,c] => c"
  "isInfinity" :: c
  "isa_lbrk_rbrk_a" :: "[c] => c"
  "isa_less_more_a" :: "[c] => c"

lemma ob'24:
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Acceptors
fixes Values
fixes Quorums
fixes Proposers
fixes sent sent'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition sent1b2b suppressed *)
(* usable definition PartialBmax suppressed *)
(* usable definition voteds suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Bmax suppressed *)
(* usable definition FreeSlots suppressed *)
(* usable definition NewProposals suppressed *)
(* usable definition ProposeDecrees suppressed *)
(* usable definition VS suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Preempt suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
fixes a
assumes a_in : "(a \<in> (Acceptors))"
fixes s
assumes s_in : "(s \<in> (Nat))"
assumes v'57: "(TypeOK)"
assumes v'64: "((((voteds ((a)))) \<in> ((SUBSET ([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])))))"
assumes v'65: "(((\<exists> r \<in> ((voteds ((a)))) : (((fapply ((r), (''slot''))) = (s)))) \<Leftrightarrow> (\<exists> r \<in> ((PartialBmax (((voteds ((a))))))) : (((fapply ((r), (''slot''))) = (s))))))"
assumes v'66: "((((PartialBmax (((voteds ((a))))))) \<subseteq> ((voteds ((a))))))"
assumes v'67: "(\<forall> r \<in> ((voteds ((a)))) : (\<forall> a_s2a \<in> (Nat) : (((((fapply ((r), (''slot''))) = (a_s2a))) \<Rightarrow> (\<exists> a_r2a \<in> ((PartialBmax (((voteds ((a))))))) : (((((fapply ((a_r2a), (''slot''))) = (a_s2a))) \<and> ((leq ((fapply ((r), (''bal''))), (fapply ((a_r2a), (''bal'')))))))))))))"
shows "(((((voteds ((a)))) \<in> ((SUBSET ([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)]))))) & (((\<exists> r \<in> ((voteds ((a)))) : (((fapply ((r), (''slot''))) = (s)))) \<Leftrightarrow> (\<exists> r \<in> ((PartialBmax (((voteds ((a))))))) : (((fapply ((r), (''slot''))) = (s)))))) & ((((PartialBmax (((voteds ((a))))))) \<subseteq> ((voteds ((a)))))) & (\<forall> r \<in> ((voteds ((a)))) : (\<exists> a_r2a \<in> ((PartialBmax (((voteds ((a))))))) : (((((fapply ((r), (''slot''))) = (fapply ((a_r2a), (''slot''))))) \<and> ((leq ((fapply ((r), (''bal''))), (fapply ((a_r2a), (''bal'')))))))))))"(is "PROP ?ob'24")
proof -
ML_command {* writeln "*** TLAPS ENTER 24"; *}
show "PROP ?ob'24"

(* BEGIN ZENON INPUT
;; file=MultiPaxosUs.tlaps/tlapm_6ac7d9.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >MultiPaxosUs.tlaps/tlapm_6ac7d9.znn.out
;; obligation #24
$hyp "a_in" (TLA.in a Acceptors)
$hyp "s_in" (TLA.in s arith.N)
$hyp "v'57" TypeOK
$hyp "v'64" (TLA.in (voteds a)
(TLA.SUBSET (TLA.recordset "bal" arith.N "slot" arith.N "val" Values)))
$hyp "v'65" (<=> (TLA.bEx (voteds a) ((r) (= (TLA.fapply r "slot") s)))
(TLA.bEx (PartialBmax (voteds a)) ((r) (= (TLA.fapply r "slot")
s))))
$hyp "v'66" (TLA.subseteq (PartialBmax (voteds a))
(voteds a))
$hyp "v'67" (TLA.bAll (voteds a) ((r) (TLA.bAll arith.N ((a_s2a) (=> (= (TLA.fapply r "slot")
a_s2a)
(TLA.bEx (PartialBmax (voteds a)) ((a_r2a) (/\ (= (TLA.fapply a_r2a "slot")
a_s2a) (arith.le (TLA.fapply r "bal")
(TLA.fapply a_r2a "bal"))))))))))
$goal (/\ (TLA.in (voteds a)
(TLA.SUBSET (TLA.recordset "bal" arith.N "slot" arith.N "val" Values)))
(<=> (TLA.bEx (voteds a) ((r) (= (TLA.fapply r "slot") s)))
(TLA.bEx (PartialBmax (voteds a)) ((r) (= (TLA.fapply r "slot") s))))
(TLA.subseteq (PartialBmax (voteds a)) (voteds a))
(TLA.bAll (voteds a) ((r) (TLA.bEx (PartialBmax (voteds a)) ((a_r2a) (/\ (= (TLA.fapply r "slot")
(TLA.fapply a_r2a "slot")) (arith.le (TLA.fapply r "bal")
(TLA.fapply a_r2a "bal"))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hg:"bAll(voteds(a), (\<lambda>r. bAll(Nat, (\<lambda>a_s2a. (((r[''slot''])=a_s2a)=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((a_r2a[''slot''])=a_s2a)&((r[''bal'']) <= (a_r2a[''bal'']))))))))))" (is "?z_hg")
 using v'67 by blast
 have z_Hd:"(voteds(a) \\in SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)]))" (is "?z_hd")
 using v'64 by blast
 have z_He:"(bEx(voteds(a), (\<lambda>r. ((r[''slot''])=s)))<=>bEx(PartialBmax(voteds(a)), (\<lambda>r. ((r[''slot''])=s))))" (is "?z_hbj<=>?z_hbn")
 using v'65 by blast
 have z_Hf:"(PartialBmax(voteds(a)) \\subseteq voteds(a))" (is "?z_hf")
 using v'66 by blast
 assume z_Hh:"(~(?z_hd&((?z_hbj<=>?z_hbn)&(?z_hf&bAll(voteds(a), (\<lambda>r. bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((r[''slot''])=(a_r2a[''slot'']))&((r[''bal'']) <= (a_r2a[''bal''])))))))))))" (is "~(_&?z_hbp)")
 have z_Hbx: "(voteds(a) \\subseteq [''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])" (is "?z_hbx")
 by (rule zenon_in_SUBSET_0 [of "voteds(a)" "[''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)]", OF z_Hd])
 have z_Hby_z_Hbx: "bAll(voteds(a), (\<lambda>x. (x \\in [''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)]))) == ?z_hbx" (is "?z_hby == _")
 by (unfold subset_def)
 have z_Hby: "?z_hby"
 by (unfold z_Hby_z_Hbx, fact z_Hbx)
 have z_Hcc_z_Hg: "(\\A x:((x \\in voteds(a))=>bAll(Nat, (\<lambda>a_s2a. (((x[''slot''])=a_s2a)=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((a_r2a[''slot''])=a_s2a)&((x[''bal'']) <= (a_r2a[''bal''])))))))))) == ?z_hg" (is "?z_hcc == _")
 by (unfold bAll_def)
 have z_Hcc: "?z_hcc" (is "\\A x : ?z_hcp(x)")
 by (unfold z_Hcc_z_Hg, fact z_Hg)
 show FALSE
 proof (rule zenon_notand [OF z_Hh])
  assume z_Hcq:"(~?z_hd)"
  show FALSE
  by (rule notE [OF z_Hcq z_Hd])
 next
  assume z_Hcr:"(~?z_hbp)" (is "~(?z_he&?z_hbq)")
  show FALSE
  proof (rule zenon_notand [OF z_Hcr])
   assume z_Hcs:"(~?z_he)"
   show FALSE
   by (rule notE [OF z_Hcs z_He])
  next
   assume z_Hct:"(~?z_hbq)" (is "~(_&?z_hbr)")
   show FALSE
   proof (rule zenon_notand [OF z_Hct])
    assume z_Hcu:"(~?z_hf)"
    show FALSE
    by (rule notE [OF z_Hcu z_Hf])
   next
    assume z_Hcv:"(~?z_hbr)"
    have z_Hcw_z_Hcv: "(~(\\A x:((x \\in voteds(a))=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))&((x[''bal'']) <= (a_r2a[''bal''])))))))) == (~?z_hbr)" (is "?z_hcw == ?z_hcv")
    by (unfold bAll_def)
    have z_Hcw: "?z_hcw" (is "~(\\A x : ?z_hdd(x))")
    by (unfold z_Hcw_z_Hcv, fact z_Hcv)
    have z_Hde: "(\\E x:(~((x \\in voteds(a))=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))&((x[''bal'']) <= (a_r2a[''bal'']))))))))" (is "\\E x : ?z_hdg(x)")
    by (rule zenon_notallex_0 [of "?z_hdd", OF z_Hcw])
    have z_Hdh: "?z_hdg((CHOOSE x:(~((x \\in voteds(a))=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))&((x[''bal'']) <= (a_r2a[''bal''])))))))))" (is "~(?z_hdj=>?z_hdk)")
    by (rule zenon_ex_choose_0 [of "?z_hdg", OF z_Hde])
    have z_Hdj: "?z_hdj"
    by (rule zenon_notimply_0 [OF z_Hdh])
    have z_Hdl: "(~?z_hdk)"
    by (rule zenon_notimply_1 [OF z_Hdh])
    have z_Hdm_z_Hdl: "(~(\\E x:((x \\in PartialBmax(voteds(a)))&((((CHOOSE x:(~((x \\in voteds(a))=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))&((x[''bal'']) <= (a_r2a[''bal'']))))))))[''slot''])=(x[''slot'']))&(((CHOOSE x:(~((x \\in voteds(a))=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))&((x[''bal'']) <= (a_r2a[''bal'']))))))))[''bal'']) <= (x[''bal''])))))) == (~?z_hdk)" (is "?z_hdm == ?z_hdl")
    by (unfold bEx_def)
    have z_Hdm: "?z_hdm" (is "~(\\E x : ?z_hdv(x))")
    by (unfold z_Hdm_z_Hdl, fact z_Hdl)
    have z_Hdw: "?z_hcp((CHOOSE x:(~((x \\in voteds(a))=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))&((x[''bal'']) <= (a_r2a[''bal''])))))))))" (is "_=>?z_hdx")
    by (rule zenon_all_0 [of "?z_hcp" "(CHOOSE x:(~((x \\in voteds(a))=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))&((x[''bal'']) <= (a_r2a[''bal'']))))))))", OF z_Hcc])
    show FALSE
    proof (rule zenon_imply [OF z_Hdw])
     assume z_Hdy:"(~?z_hdj)"
     show FALSE
     by (rule notE [OF z_Hdy z_Hdj])
    next
     assume z_Hdx:"?z_hdx"
     have z_Hdz_z_Hdx: "(\\A x:((x \\in Nat)=>((((CHOOSE x:(~((x \\in voteds(a))=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))&((x[''bal'']) <= (a_r2a[''bal'']))))))))[''slot''])=x)=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((a_r2a[''slot''])=x)&(((CHOOSE x:(~((x \\in voteds(a))=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))&((x[''bal'']) <= (a_r2a[''bal'']))))))))[''bal'']) <= (a_r2a[''bal''])))))))) == ?z_hdx" (is "?z_hdz == _")
     by (unfold bAll_def)
     have z_Hdz: "?z_hdz" (is "\\A x : ?z_hej(x)")
     by (unfold z_Hdz_z_Hdx, fact z_Hdx)
     have z_Hek: "?z_hej(((CHOOSE x:(~((x \\in voteds(a))=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))&((x[''bal'']) <= (a_r2a[''bal'']))))))))[''slot'']))" (is "?z_hel=>?z_hem")
     by (rule zenon_all_0 [of "?z_hej" "((CHOOSE x:(~((x \\in voteds(a))=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))&((x[''bal'']) <= (a_r2a[''bal'']))))))))[''slot''])", OF z_Hdz])
     show FALSE
     proof (rule zenon_imply [OF z_Hek])
      assume z_Hen:"(~?z_hel)"
      have z_Heo: "((CHOOSE x:(~((x \\in voteds(a))=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))&((x[''bal'']) <= (a_r2a[''bal''])))))))) \\in [''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])" (is "?z_heo")
      by (rule zenon_all_in_0 [of "voteds(a)" "(\<lambda>x. (x \\in [''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)]))", OF z_Hby z_Hdj])
      let ?z_hdi = "(CHOOSE x:(~((x \\in voteds(a))=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))&((x[''bal'']) <= (a_r2a[''bal'']))))))))"
      let ?z_hep = "<<''bal'', ''slot'', ''val''>>"
      let ?z_heq = "<<Nat, Nat, Values>>"
      have z_Her: "(2 \\in DOMAIN(?z_hep))" by auto
      have z_Heu: "((?z_hdi[(?z_hep[2])]) \\in (?z_heq[2]))" (is "?z_heu")
      by (rule zenon_in_recordset_field [OF z_Heo z_Her])
      have z_Hel: "?z_hel"
      using z_Heu by auto
      show FALSE
      by (rule notE [OF z_Hen z_Hel])
     next
      assume z_Hem:"?z_hem" (is "?z_hey=>?z_hez")
      show FALSE
      proof (rule zenon_imply [OF z_Hem])
       assume z_Hfa:"(((CHOOSE x:(~((x \\in voteds(a))=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))&((x[''bal'']) <= (a_r2a[''bal'']))))))))[''slot''])~=((CHOOSE x:(~((x \\in voteds(a))=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))&((x[''bal'']) <= (a_r2a[''bal'']))))))))[''slot'']))" (is "?z_hds~=_")
       show FALSE
       by (rule zenon_noteq [OF z_Hfa])
      next
       assume z_Hez:"?z_hez"
       have z_Hfb_z_Hez: "(\\E x:((x \\in PartialBmax(voteds(a)))&(((x[''slot''])=((CHOOSE x:(~((x \\in voteds(a))=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))&((x[''bal'']) <= (a_r2a[''bal'']))))))))[''slot'']))&(((CHOOSE x:(~((x \\in voteds(a))=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))&((x[''bal'']) <= (a_r2a[''bal'']))))))))[''bal'']) <= (x[''bal'']))))) == ?z_hez" (is "?z_hfb == _")
       by (unfold bEx_def)
       have z_Hfb: "?z_hfb" (is "\\E x : ?z_hff(x)")
       by (unfold z_Hfb_z_Hez, fact z_Hez)
       have z_Hfg: "?z_hff((CHOOSE x:((x \\in PartialBmax(voteds(a)))&(((x[''slot''])=((CHOOSE x:(~((x \\in voteds(a))=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))&((x[''bal'']) <= (a_r2a[''bal'']))))))))[''slot'']))&(((CHOOSE x:(~((x \\in voteds(a))=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))&((x[''bal'']) <= (a_r2a[''bal'']))))))))[''bal'']) <= (x[''bal'']))))))" (is "?z_hfi&?z_hfj")
       by (rule zenon_ex_choose_0 [of "?z_hff", OF z_Hfb])
       have z_Hfi: "?z_hfi"
       by (rule zenon_and_0 [OF z_Hfg])
       have z_Hfj: "?z_hfj" (is "?z_hfk&?z_hfl")
       by (rule zenon_and_1 [OF z_Hfg])
       have z_Hfk: "?z_hfk" (is "?z_hfm=?z_hds")
       by (rule zenon_and_0 [OF z_Hfj])
       have z_Hfl: "?z_hfl"
       by (rule zenon_and_1 [OF z_Hfj])
       have z_Hfn: "~?z_hdv((CHOOSE x:((x \\in PartialBmax(voteds(a)))&(((x[''slot''])=?z_hds)&(((CHOOSE x:(~((x \\in voteds(a))=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))&((x[''bal'']) <= (a_r2a[''bal'']))))))))[''bal'']) <= (x[''bal'']))))))" (is "~(_&?z_hfo)")
       by (rule zenon_notex_0 [of "?z_hdv" "(CHOOSE x:((x \\in PartialBmax(voteds(a)))&(((x[''slot''])=?z_hds)&(((CHOOSE x:(~((x \\in voteds(a))=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))&((x[''bal'']) <= (a_r2a[''bal'']))))))))[''bal'']) <= (x[''bal''])))))", OF z_Hdm])
       show FALSE
       proof (rule zenon_notand [OF z_Hfn])
        assume z_Hfp:"(~?z_hfi)"
        show FALSE
        by (rule notE [OF z_Hfp z_Hfi])
       next
        assume z_Hfq:"(~?z_hfo)" (is "~(?z_hfr&_)")
        show FALSE
        proof (rule zenon_notand [OF z_Hfq])
         assume z_Hfs:"(?z_hds~=?z_hfm)"
         show FALSE
         by (rule zenon_eqsym [OF z_Hfk z_Hfs])
        next
         assume z_Hft:"(~?z_hfl)"
         show FALSE
         by (rule notE [OF z_Hft z_Hfl])
        qed
       qed
      qed
     qed
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 24"; *} qed
lemma ob'31:
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Acceptors
fixes Values
fixes Quorums
fixes Proposers
fixes sent sent'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition sent1b2b suppressed *)
(* usable definition PartialBmax suppressed *)
(* usable definition voteds suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Bmax suppressed *)
(* usable definition FreeSlots suppressed *)
(* usable definition NewProposals suppressed *)
(* usable definition ProposeDecrees suppressed *)
(* usable definition VS suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Preempt suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
fixes a
assumes a_in : "(a \<in> (Acceptors))"
fixes s
assumes s_in : "(s \<in> (Nat))"
assumes v'57: "(TypeOK)"
assumes v'63: "(\<forall> S \<in> ((SUBSET ([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)]))) : (\<forall> s_1 \<in> (Nat) : (((\<exists> r \<in> (S) : (((fapply ((r), (''slot''))) = (s_1)))) \<Leftrightarrow> (\<exists> r \<in> ((PartialBmax ((S)))) : (((fapply ((r), (''slot''))) = (s_1))))))))"
assumes v'64: "((((voteds ((a)))) \<in> ((SUBSET ([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])))))"
shows "(((\<exists> r \<in> ((voteds ((a)))) : (((fapply ((r), (''slot''))) = (s)))) \<Leftrightarrow> (\<exists> r \<in> ((PartialBmax (((voteds ((a))))))) : (((fapply ((r), (''slot''))) = (s))))))"(is "PROP ?ob'31")
proof -
ML_command {* writeln "*** TLAPS ENTER 31"; *}
show "PROP ?ob'31"

(* BEGIN ZENON INPUT
;; file=MultiPaxosUs.tlaps/tlapm_1b504c.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >MultiPaxosUs.tlaps/tlapm_1b504c.znn.out
;; obligation #31
$hyp "a_in" (TLA.in a Acceptors)
$hyp "s_in" (TLA.in s arith.N)
$hyp "v'57" TypeOK
$hyp "v'63" (TLA.bAll (TLA.SUBSET (TLA.recordset "bal" arith.N "slot" arith.N "val" Values)) ((S) (TLA.bAll arith.N ((s_1) (<=> (TLA.bEx S ((r) (= (TLA.fapply r "slot")
s_1))) (TLA.bEx (PartialBmax S) ((r) (= (TLA.fapply r "slot")
s_1))))))))
$hyp "v'64" (TLA.in (voteds a)
(TLA.SUBSET (TLA.recordset "bal" arith.N "slot" arith.N "val" Values)))
$goal (<=> (TLA.bEx (voteds a) ((r) (= (TLA.fapply r "slot") s)))
(TLA.bEx (PartialBmax (voteds a)) ((r) (= (TLA.fapply r "slot")
s))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"bAll(SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)]), (\<lambda>S. bAll(Nat, (\<lambda>s_1. (bEx(S, (\<lambda>r. ((r[''slot''])=s_1)))<=>bEx(PartialBmax(S), (\<lambda>r. ((r[''slot''])=s_1))))))))" (is "?z_hd")
 using v'63 by blast
 have z_Hb:"(s \\in Nat)" (is "?z_hb")
 using s_in by blast
 have z_He:"(voteds(a) \\in SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)]))" (is "?z_he")
 using v'64 by blast
 assume z_Hf:"(~(bEx(voteds(a), (\<lambda>r. ((r[''slot''])=s)))<=>bEx(PartialBmax(voteds(a)), (\<lambda>r. ((r[''slot''])=s)))))" (is "~(?z_hbe<=>?z_hbh)")
 have z_Hbj_z_Hd: "(\\A x:((x \\in SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)]))=>bAll(Nat, (\<lambda>s_1. (bEx(x, (\<lambda>r. ((r[''slot''])=s_1)))<=>bEx(PartialBmax(x), (\<lambda>r. ((r[''slot''])=s_1)))))))) == ?z_hd" (is "?z_hbj == _")
 by (unfold bAll_def)
 have z_Hbj: "?z_hbj" (is "\\A x : ?z_hbt(x)")
 by (unfold z_Hbj_z_Hd, fact z_Hd)
 have z_Hbu: "?z_hbt(voteds(a))" (is "_=>?z_hbv")
 by (rule zenon_all_0 [of "?z_hbt" "voteds(a)", OF z_Hbj])
 show FALSE
 proof (rule zenon_imply [OF z_Hbu])
  assume z_Hbw:"(~?z_he)"
  show FALSE
  by (rule notE [OF z_Hbw z_He])
 next
  assume z_Hbv:"?z_hbv"
  have z_Hbx_z_Hbv: "(\\A x:((x \\in Nat)=>(bEx(voteds(a), (\<lambda>r. ((r[''slot''])=x)))<=>bEx(PartialBmax(voteds(a)), (\<lambda>r. ((r[''slot''])=x)))))) == ?z_hbv" (is "?z_hbx == _")
  by (unfold bAll_def)
  have z_Hbx: "?z_hbx" (is "\\A x : ?z_hcf(x)")
  by (unfold z_Hbx_z_Hbv, fact z_Hbv)
  have z_Hcg: "?z_hcf(s)" (is "_=>?z_hbd")
  by (rule zenon_all_0 [of "?z_hcf" "s", OF z_Hbx])
  show FALSE
  proof (rule zenon_imply [OF z_Hcg])
   assume z_Hch:"(~?z_hb)"
   show FALSE
   by (rule notE [OF z_Hch z_Hb])
  next
   assume z_Hbd:"?z_hbd"
   show FALSE
   by (rule notE [OF z_Hf z_Hbd])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 31"; *} qed
lemma ob'8:
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Acceptors
fixes Values
fixes Quorums
fixes Proposers
(* usable definition Ballots suppressed *)
(* usable definition Slots suppressed *)
fixes sent sent'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition sent1b2b suppressed *)
(* usable definition PartialBmax suppressed *)
(* usable definition voteds suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Bmax suppressed *)
(* usable definition NewProposals suppressed *)
(* usable definition ProposeDecrees suppressed *)
(* usable definition VS suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Preempt suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
fixes S
shows "(\<exists> T \<in> ((((SUBSET ([''slot'' : (subsetOf((Slots), %s. ((~ (\<exists> t \<in> (S) : (((fapply ((t), (''slot''))) = (s)))))))), ''val'' : (Values)]))) \\ ({}))) : (\<forall> a_t1a \<in> (T) : (\<forall> a_t2a \<in> (T) : (((((fapply ((a_t1a), (''slot''))) = (fapply ((a_t2a), (''slot''))))) \<Rightarrow> (((a_t1a) = (a_t2a))))))))"(is "PROP ?ob'8")
proof -
ML_command {* writeln "*** TLAPS ENTER 8"; *}
show "PROP ?ob'8"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 8"; *} qed
lemma ob'43:
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Acceptors
fixes Values
fixes Quorums
fixes Proposers
(* usable definition Ballots suppressed *)
(* usable definition Slots suppressed *)
fixes sent sent'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition sent1b2b suppressed *)
(* usable definition PartialBmax suppressed *)
(* usable definition voteds suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Bmax suppressed *)
(* usable definition FreeSlots suppressed *)
(* usable definition NewProposals suppressed *)
(* usable definition ProposeDecrees suppressed *)
(* usable definition VS suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Preempt suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
(* usable definition Inv suppressed *)
fixes p
assumes p_in : "(p \<in> (Proposers))"
assumes v'61: "(\<exists> b \<in> (Ballots) : (((~ (\<exists> m \<in> (sent) : (((((fapply ((m), (''type''))) = (''2a''))) \<and> (((fapply ((m), (''bal''))) = (b)))))))) & (\<exists> Q \<in> (Quorums) : (\<exists> S \<in> ((SUBSET (subsetOf((sent), %m. (((((fapply ((m), (''type''))) = (''1b''))) \<and> (((fapply ((m), (''bal''))) = (b))))))))) : ((\<forall> a \<in> (Q) : (\<exists> m \<in> (S) : (((fapply ((m), (''from''))) = (a))))) & ((Send (({(((''type'' :> (''2a'')) @@ (''from'' :> (p)) @@ (''bal'' :> (b)) @@ (''decrees'' :> ((ProposeDecrees (((VS ((S), (Q))))))))))})))))))))"
shows "(\<exists> b \<in> (Ballots) : (\<exists> Q \<in> (Quorums) : (\<exists> S \<in> ((SUBSET (sent))) : (((~ (\<exists> a_m2a \<in> (sent) : (((((fapply ((a_m2a), (''type''))) = (''2a''))) \<and> (((fapply ((a_m2a), (''bal''))) = (b)))))))) & (((S) \<in> ((SUBSET (subsetOf((sent), %a_m2a. (((((fapply ((a_m2a), (''type''))) = (''1b''))) \<and> (((fapply ((a_m2a), (''bal''))) = (b))))))))))) & (\<forall> a \<in> (Q) : (\<exists> a_m2a \<in> (S) : (((fapply ((a_m2a), (''from''))) = (a))))) & ((Send (({(((''type'' :> (''2a'')) @@ (''bal'' :> (b)) @@ (''from'' :> (p)) @@ (''decrees'' :> ((ProposeDecrees (((VS ((S), (Q))))))))))}))))))))"(is "PROP ?ob'43")
proof -
ML_command {* writeln "*** TLAPS ENTER 43"; *}
show "PROP ?ob'43"

(* BEGIN ZENON INPUT
;; file=MultiPaxosUs.tlaps/tlapm_24d9de.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >MultiPaxosUs.tlaps/tlapm_24d9de.znn.out
;; obligation #43
$hyp "p_in" (TLA.in p Proposers)
$hyp "v'61" (TLA.bEx Ballots ((b) (/\ (-. (TLA.bEx sent ((m) (/\ (= (TLA.fapply m "type")
"2a") (= (TLA.fapply m "bal") b)))))
(TLA.bEx Quorums ((Q) (TLA.bEx (TLA.SUBSET (TLA.subsetOf sent ((m) (/\ (= (TLA.fapply m "type")
"1b") (= (TLA.fapply m "bal")
b))))) ((S) (/\ (TLA.bAll Q ((a) (TLA.bEx S ((m) (= (TLA.fapply m "from")
a)))))
(Send (TLA.set (TLA.record "type" "2a" "from" p "bal" b "decrees" (ProposeDecrees (VS S
Q)))))))))))))
$goal (TLA.bEx Ballots ((b) (TLA.bEx Quorums ((Q) (TLA.bEx (TLA.SUBSET sent) ((S) (/\ (-. (TLA.bEx sent ((a_m2a) (/\ (= (TLA.fapply a_m2a "type")
"2a") (= (TLA.fapply a_m2a "bal") b))))) (TLA.in S
(TLA.SUBSET (TLA.subsetOf sent ((a_m2a) (/\ (= (TLA.fapply a_m2a "type")
"1b") (= (TLA.fapply a_m2a "bal") b))))))
(TLA.bAll Q ((a) (TLA.bEx S ((a_m2a) (= (TLA.fapply a_m2a "from") a)))))
(Send (TLA.set (TLA.record "type" "2a" "bal" b "from" p "decrees" (ProposeDecrees (VS S
Q))))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hb:"bEx(Ballots, (\<lambda>b. ((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=b)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=b))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (b) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))" (is "?z_hb")
 using v'61 by blast
 assume z_Hc:"(~bEx(Ballots, (\<lambda>b. bEx(Quorums, (\<lambda>Q. bEx(SUBSET(sent), (\<lambda>S. ((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=b)))))&((S \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=b))))))&(bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''from'' :> (p) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))" (is "~?z_hbx")
 have z_Hcl_z_Hb: "(\\E x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))}))))))))) == ?z_hb" (is "?z_hcl == _")
 by (unfold bEx_def)
 have z_Hcl: "?z_hcl" (is "\\E x : ?z_hdh(x)")
 by (unfold z_Hcl_z_Hb, fact z_Hb)
 have z_Hdi: "?z_hdh((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))}))))))))))" (is "?z_hdk&?z_hdl")
 by (rule zenon_ex_choose_0 [of "?z_hdh", OF z_Hcl])
 have z_Hdk: "?z_hdk"
 by (rule zenon_and_0 [OF z_Hdi])
 have z_Hdl: "?z_hdl" (is "?z_hdm&?z_hdn")
 by (rule zenon_and_1 [OF z_Hdi])
 have z_Hdm: "?z_hdm" (is "~?z_hdo")
 by (rule zenon_and_0 [OF z_Hdl])
 have z_Hdn: "?z_hdn"
 by (rule zenon_and_1 [OF z_Hdl])
 have z_Hdp_z_Hdn: "(\\E x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))) == ?z_hdn" (is "?z_hdp == _")
 by (unfold bEx_def)
 have z_Hdp: "?z_hdp" (is "\\E x : ?z_heg(x)")
 by (unfold z_Hdp_z_Hdn, fact z_Hdn)
 have z_Heh: "?z_heg((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))))" (is "?z_hej&?z_hek")
 by (rule zenon_ex_choose_0 [of "?z_heg", OF z_Hdp])
 have z_Hej: "?z_hej"
 by (rule zenon_and_0 [OF z_Heh])
 have z_Hek: "?z_hek"
 by (rule zenon_and_1 [OF z_Heh])
 have z_Hel_z_Hek: "(\\E x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))) == ?z_hek" (is "?z_hel == _")
 by (unfold bEx_def)
 have z_Hel: "?z_hel" (is "\\E x : ?z_hex(x)")
 by (unfold z_Hel_z_Hek, fact z_Hek)
 have z_Hey: "?z_hex((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))" (is "?z_hfa&?z_hfb")
 by (rule zenon_ex_choose_0 [of "?z_hex", OF z_Hel])
 have z_Hfa: "?z_hfa"
 by (rule zenon_and_0 [OF z_Hey])
 have z_Hfb: "?z_hfb" (is "?z_hfc&?z_hfd")
 by (rule zenon_and_1 [OF z_Hey])
 have z_Hfc: "?z_hfc"
 by (rule zenon_and_0 [OF z_Hfb])
 have z_Hfd: "?z_hfd"
 by (rule zenon_and_1 [OF z_Hfb])
 have z_Hfe: "((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))) \\subseteq subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))}))))))))))))))" (is "?z_hfe")
 by (rule zenon_in_SUBSET_0 [of "(CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))}))))" "subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))", OF z_Hfa])
 have z_Hff_z_Hfe: "bAll((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))), (\<lambda>x. (x \\in subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))) == ?z_hfe" (is "?z_hff == _")
 by (unfold subset_def)
 have z_Hff: "?z_hff"
 by (unfold z_Hff_z_Hfe, fact z_Hfe)
 have z_Hfi_z_Hff: "(\\A x:((x \\in (CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))=>(x \\in subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))) == ?z_hff" (is "?z_hfi == _")
 by (unfold bAll_def)
 have z_Hfi: "?z_hfi" (is "\\A x : ?z_hfl(x)")
 by (unfold z_Hfi_z_Hff, fact z_Hff)
 have z_Hfm_z_Hc: "(~(\\E x:((x \\in Ballots)&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(sent), (\<lambda>S. ((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&((S \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))))&(bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''bal'' :> (x) @@ ''from'' :> (p) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))}))))))))))) == (~?z_hbx)" (is "?z_hfm == ?z_hc")
 by (unfold bEx_def)
 have z_Hfm: "?z_hfm" (is "~(\\E x : ?z_hga(x))")
 by (unfold z_Hfm_z_Hc, fact z_Hc)
 have z_Hgb: "~?z_hga((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))}))))))))))" (is "~(_&?z_hgc)")
 by (rule zenon_notex_0 [of "?z_hga" "(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))", OF z_Hfm])
 show FALSE
 proof (rule zenon_notand [OF z_Hgb])
  assume z_Hgd:"(~?z_hdk)"
  show FALSE
  by (rule notE [OF z_Hgd z_Hdk])
 next
  assume z_Hge:"(~?z_hgc)"
  have z_Hgf_z_Hge: "(~(\\E x:((x \\in Quorums)&bEx(SUBSET(sent), (\<lambda>S. (?z_hdm&((S \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''from'' :> (p) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))) == (~?z_hgc)" (is "?z_hgf == ?z_hge")
  by (unfold bEx_def)
  have z_Hgf: "?z_hgf" (is "~(\\E x : ?z_hgr(x))")
  by (unfold z_Hgf_z_Hge, fact z_Hge)
  have z_Hgs: "~?z_hgr((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))))" (is "~(_&?z_hgt)")
  by (rule zenon_notex_0 [of "?z_hgr" "(CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))", OF z_Hgf])
  show FALSE
  proof (rule zenon_notand [OF z_Hgs])
   assume z_Hgu:"(~?z_hej)"
   show FALSE
   by (rule notE [OF z_Hgu z_Hej])
  next
   assume z_Hgv:"(~?z_hgt)"
   have z_Hgw_z_Hgv: "(~(\\E x:((x \\in SUBSET(sent))&(?z_hdm&((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''from'' :> (p) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))}))))))) == (~?z_hgt)" (is "?z_hgw == ?z_hgv")
   by (unfold bEx_def)
   have z_Hgw: "?z_hgw" (is "~(\\E x : ?z_hhg(x))")
   by (unfold z_Hgw_z_Hgv, fact z_Hgv)
   have z_Hhh: "~?z_hhg((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))" (is "~(?z_hhi&?z_hhj)")
   by (rule zenon_notex_0 [of "?z_hhg" "(CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))}))))", OF z_Hgw])
   show FALSE
   proof (rule zenon_notand [OF z_Hhh])
    assume z_Hhk:"(~?z_hhi)"
    have z_Hhl: "(~((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))) \\subseteq sent))" (is "~?z_hhm")
    by (rule zenon_notin_SUBSET_0 [of "(CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))}))))" "sent", OF z_Hhk])
    have z_Hhn_z_Hhl: "(~bAll((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))), (\<lambda>zenon_Vdb. (zenon_Vdb \\in sent)))) == (~?z_hhm)" (is "?z_hhn == ?z_hhl")
    by (unfold subset_def)
    have z_Hhn: "?z_hhn" (is "~?z_hho")
    by (unfold z_Hhn_z_Hhl, fact z_Hhl)
    have z_Hhs_z_Hhn: "(~(\\A x:((x \\in (CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))=>(x \\in sent)))) == ?z_hhn" (is "?z_hhs == _")
    by (unfold bAll_def)
    have z_Hhs: "?z_hhs" (is "~(\\A x : ?z_hhw(x))")
    by (unfold z_Hhs_z_Hhn, fact z_Hhn)
    have z_Hhx: "(\\E x:(~((x \\in (CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))=>(x \\in sent))))" (is "\\E x : ?z_hhz(x)")
    by (rule zenon_notallex_0 [of "?z_hhw", OF z_Hhs])
    have z_Hia: "?z_hhz((CHOOSE x:(~((x \\in (CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))=>(x \\in sent)))))" (is "~(?z_hic=>?z_hid)")
    by (rule zenon_ex_choose_0 [of "?z_hhz", OF z_Hhx])
    have z_Hic: "?z_hic"
    by (rule zenon_notimply_0 [OF z_Hia])
    have z_Hie: "(~?z_hid)"
    by (rule zenon_notimply_1 [OF z_Hia])
    have z_Hif: "?z_hfl((CHOOSE x:(~((x \\in (CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))=>(x \\in sent)))))" (is "_=>?z_hig")
    by (rule zenon_all_0 [of "?z_hfl" "(CHOOSE x:(~((x \\in (CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))=>(x \\in sent))))", OF z_Hfi])
    show FALSE
    proof (rule zenon_imply [OF z_Hif])
     assume z_Hih:"(~?z_hic)"
     show FALSE
     by (rule notE [OF z_Hih z_Hic])
    next
     assume z_Hig:"?z_hig"
     have z_Hid: "?z_hid"
     by (rule zenon_in_subsetof_0 [of "(CHOOSE x:(~((x \\in (CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))=>(x \\in sent))))" "sent" "(\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))}))))))))))))", OF z_Hig])
     show FALSE
     by (rule notE [OF z_Hie z_Hid])
    qed
   next
    assume z_Hii:"(~?z_hhj)" (is "~(_&?z_hij)")
    show FALSE
    proof (rule zenon_notand [OF z_Hii])
     assume z_Hik:"(~?z_hdm)"
     show FALSE
     by (rule notE [OF z_Hik z_Hdm])
    next
     assume z_Hil:"(~?z_hij)" (is "~(_&?z_him)")
     show FALSE
     proof (rule zenon_notand [OF z_Hil])
      assume z_Hin:"(~?z_hfa)"
      show FALSE
      by (rule notE [OF z_Hin z_Hfa])
     next
      assume z_Hio:"(~?z_him)" (is "~(_&?z_hip)")
      show FALSE
      proof (rule zenon_notand [OF z_Hio])
       assume z_Hiq:"(~?z_hfc)"
       show FALSE
       by (rule notE [OF z_Hiq z_Hfc])
      next
       assume z_Hir:"(~?z_hip)"
       show FALSE
       proof (rule notE [OF z_Hir])
        have z_His: "({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))), (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))}={(''type'' :> (''2a'') @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''from'' :> (p) @@ ''decrees'' :> (ProposeDecrees(VS((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))), (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})" (is "?z_hit=?z_hix")
        proof (rule zenon_nnpp [of "(?z_hit=?z_hix)"])
         assume z_Hiz:"(?z_hit~=?z_hix)"
         show FALSE
         proof (rule zenon_noteq [of "?z_hix"])
          have z_Hja: "((''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))), (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))=(''type'' :> (''2a'') @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''from'' :> (p) @@ ''decrees'' :> (ProposeDecrees(VS((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))), (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Ballots)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))))))))" (is "?z_hiu=?z_hiy")
          proof (rule zenon_nnpp [of "(?z_hiu=?z_hiy)"])
           assume z_Hjb:"(?z_hiu~=?z_hiy)"
           sorry
          qed
          have z_Hjc: "(?z_hix~=?z_hix)"
          by (rule subst [where P="(\<lambda>zenon_Vcf. ({zenon_Vcf}~=?z_hix))", OF z_Hja], fact z_Hiz)
          thus "(?z_hix~=?z_hix)" .
         qed
        qed
        have z_Hip: "?z_hip"
        by (rule subst [where P="(\<lambda>zenon_Vdf. Send(zenon_Vdf))", OF z_His], fact z_Hfd)
        thus "?z_hip" .
       qed
      qed
     qed
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 43"; *} qed
lemma ob'35:
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Acceptors
fixes Values
fixes Quorums
fixes Proposers
fixes sent sent'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition sent1b2b suppressed *)
(* usable definition PartialBmax suppressed *)
(* usable definition voteds suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Bmax suppressed *)
(* usable definition FreeSlots suppressed *)
(* usable definition NewProposals suppressed *)
(* usable definition ProposeDecrees suppressed *)
(* usable definition VS suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Preempt suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
fixes a
assumes a_in : "(a \<in> (Acceptors))"
fixes s
assumes s_in : "(s \<in> (Nat))"
assumes v'57: "(TypeOK)"
assumes v'65: "(\<forall> S \<in> ((SUBSET ([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)]))) : (\<forall> r \<in> (S) : (\<exists> a_r2a \<in> ((PartialBmax ((S)))) : (((((fapply ((r), (''slot''))) = (fapply ((a_r2a), (''slot''))))) \<and> ((leq ((fapply ((r), (''bal''))), (fapply ((a_r2a), (''bal'')))))))))))"
assumes v'66: "((((voteds ((a)))) \<in> ((SUBSET ([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])))))"
shows "(\<forall> r \<in> ((voteds ((a)))) : (\<forall> a_s2a \<in> (Nat) : (((((fapply ((r), (''slot''))) = (a_s2a))) \<Rightarrow> (\<exists> a_r2a \<in> ((PartialBmax (((voteds ((a))))))) : (((((fapply ((a_r2a), (''slot''))) = (a_s2a))) \<and> ((leq ((fapply ((r), (''bal''))), (fapply ((a_r2a), (''bal'')))))))))))))"(is "PROP ?ob'35")
proof -
ML_command {* writeln "*** TLAPS ENTER 35"; *}
show "PROP ?ob'35"

(* BEGIN ZENON INPUT
;; file=MultiPaxosUs.tlaps/tlapm_8a858e.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >MultiPaxosUs.tlaps/tlapm_8a858e.znn.out
;; obligation #35
$hyp "a_in" (TLA.in a Acceptors)
$hyp "s_in" (TLA.in s arith.N)
$hyp "v'57" TypeOK
$hyp "v'65" (TLA.bAll (TLA.SUBSET (TLA.recordset "bal" arith.N "slot" arith.N "val" Values)) ((S) (TLA.bAll S ((r) (TLA.bEx (PartialBmax S) ((a_r2a) (/\ (= (TLA.fapply r "slot")
(TLA.fapply a_r2a "slot")) (arith.le (TLA.fapply r "bal")
(TLA.fapply a_r2a "bal")))))))))
$hyp "v'66" (TLA.in (voteds a)
(TLA.SUBSET (TLA.recordset "bal" arith.N "slot" arith.N "val" Values)))
$goal (TLA.bAll (voteds a) ((r) (TLA.bAll arith.N ((a_s2a) (=> (= (TLA.fapply r "slot")
a_s2a)
(TLA.bEx (PartialBmax (voteds a)) ((a_r2a) (/\ (= (TLA.fapply a_r2a "slot")
a_s2a) (arith.le (TLA.fapply r "bal")
(TLA.fapply a_r2a "bal"))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"bAll(SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)]), (\<lambda>S. bAll(S, (\<lambda>r. bEx(PartialBmax(S), (\<lambda>a_r2a. (((r[''slot''])=(a_r2a[''slot'']))&((r[''bal'']) <= (a_r2a[''bal''])))))))))" (is "?z_hd")
 using v'65 by blast
 have z_He:"(voteds(a) \\in SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)]))" (is "?z_he")
 using v'66 by blast
 assume z_Hf:"(~bAll(voteds(a), (\<lambda>r. bAll(Nat, (\<lambda>a_s2a. (((r[''slot''])=a_s2a)=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((a_r2a[''slot''])=a_s2a)&((r[''bal'']) <= (a_r2a[''bal''])))))))))))" (is "~?z_hbf")
 have z_Hbr_z_Hd: "(\\A x:((x \\in SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)]))=>bAll(x, (\<lambda>r. bEx(PartialBmax(x), (\<lambda>a_r2a. (((r[''slot''])=(a_r2a[''slot'']))&((r[''bal'']) <= (a_r2a[''bal'']))))))))) == ?z_hd" (is "?z_hbr == _")
 by (unfold bAll_def)
 have z_Hbr: "?z_hbr" (is "\\A x : ?z_hbz(x)")
 by (unfold z_Hbr_z_Hd, fact z_Hd)
 have z_Hca_z_Hf: "(~(\\A x:((x \\in voteds(a))=>bAll(Nat, (\<lambda>a_s2a. (((x[''slot''])=a_s2a)=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((a_r2a[''slot''])=a_s2a)&((x[''bal'']) <= (a_r2a[''bal'']))))))))))) == (~?z_hbf)" (is "?z_hca == ?z_hf")
 by (unfold bAll_def)
 have z_Hca: "?z_hca" (is "~(\\A x : ?z_hco(x))")
 by (unfold z_Hca_z_Hf, fact z_Hf)
 have z_Hcp: "(\\E x:(~((x \\in voteds(a))=>bAll(Nat, (\<lambda>a_s2a. (((x[''slot''])=a_s2a)=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((a_r2a[''slot''])=a_s2a)&((x[''bal'']) <= (a_r2a[''bal''])))))))))))" (is "\\E x : ?z_hcr(x)")
 by (rule zenon_notallex_0 [of "?z_hco", OF z_Hca])
 have z_Hcs: "?z_hcr((CHOOSE x:(~((x \\in voteds(a))=>bAll(Nat, (\<lambda>a_s2a. (((x[''slot''])=a_s2a)=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((a_r2a[''slot''])=a_s2a)&((x[''bal'']) <= (a_r2a[''bal'']))))))))))))" (is "~(?z_hcu=>?z_hcv)")
 by (rule zenon_ex_choose_0 [of "?z_hcr", OF z_Hcp])
 have z_Hcu: "?z_hcu"
 by (rule zenon_notimply_0 [OF z_Hcs])
 have z_Hcw: "(~?z_hcv)"
 by (rule zenon_notimply_1 [OF z_Hcs])
 have z_Hcx_z_Hcw: "(~(\\A x:((x \\in Nat)=>((((CHOOSE x:(~((x \\in voteds(a))=>bAll(Nat, (\<lambda>a_s2a. (((x[''slot''])=a_s2a)=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((a_r2a[''slot''])=a_s2a)&((x[''bal'']) <= (a_r2a[''bal''])))))))))))[''slot''])=x)=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((a_r2a[''slot''])=x)&(((CHOOSE x:(~((x \\in voteds(a))=>bAll(Nat, (\<lambda>a_s2a. (((x[''slot''])=a_s2a)=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((a_r2a[''slot''])=a_s2a)&((x[''bal'']) <= (a_r2a[''bal''])))))))))))[''bal'']) <= (a_r2a[''bal'']))))))))) == (~?z_hcv)" (is "?z_hcx == ?z_hcw")
 by (unfold bAll_def)
 have z_Hcx: "?z_hcx" (is "~(\\A x : ?z_hdk(x))")
 by (unfold z_Hcx_z_Hcw, fact z_Hcw)
 have z_Hdl: "(\\E x:(~((x \\in Nat)=>((((CHOOSE x:(~((x \\in voteds(a))=>bAll(Nat, (\<lambda>a_s2a. (((x[''slot''])=a_s2a)=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((a_r2a[''slot''])=a_s2a)&((x[''bal'']) <= (a_r2a[''bal''])))))))))))[''slot''])=x)=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((a_r2a[''slot''])=x)&(((CHOOSE x:(~((x \\in voteds(a))=>bAll(Nat, (\<lambda>a_s2a. (((x[''slot''])=a_s2a)=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((a_r2a[''slot''])=a_s2a)&((x[''bal'']) <= (a_r2a[''bal''])))))))))))[''bal'']) <= (a_r2a[''bal''])))))))))" (is "\\E x : ?z_hdn(x)")
 by (rule zenon_notallex_0 [of "?z_hdk", OF z_Hcx])
 have z_Hdo: "?z_hdn((CHOOSE x:(~((x \\in Nat)=>((((CHOOSE x:(~((x \\in voteds(a))=>bAll(Nat, (\<lambda>a_s2a. (((x[''slot''])=a_s2a)=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((a_r2a[''slot''])=a_s2a)&((x[''bal'']) <= (a_r2a[''bal''])))))))))))[''slot''])=x)=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((a_r2a[''slot''])=x)&(((CHOOSE x:(~((x \\in voteds(a))=>bAll(Nat, (\<lambda>a_s2a. (((x[''slot''])=a_s2a)=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((a_r2a[''slot''])=a_s2a)&((x[''bal'']) <= (a_r2a[''bal''])))))))))))[''bal'']) <= (a_r2a[''bal'']))))))))))" (is "~(?z_hdq=>?z_hdr)")
 by (rule zenon_ex_choose_0 [of "?z_hdn", OF z_Hdl])
 have z_Hds: "(~?z_hdr)" (is "~(?z_hdt=>?z_hdu)")
 by (rule zenon_notimply_1 [OF z_Hdo])
 have z_Hdt: "?z_hdt" (is "?z_hdd=?z_hdp")
 by (rule zenon_notimply_0 [OF z_Hds])
 have z_Hdv: "(~?z_hdu)"
 by (rule zenon_notimply_1 [OF z_Hds])
 have z_Hdw_z_Hdv: "(~(\\E x:((x \\in PartialBmax(voteds(a)))&(((x[''slot''])=?z_hdp)&(((CHOOSE x:(~((x \\in voteds(a))=>bAll(Nat, (\<lambda>a_s2a. (((x[''slot''])=a_s2a)=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((a_r2a[''slot''])=a_s2a)&((x[''bal'']) <= (a_r2a[''bal''])))))))))))[''bal'']) <= (x[''bal''])))))) == (~?z_hdu)" (is "?z_hdw == ?z_hdv")
 by (unfold bEx_def)
 have z_Hdw: "?z_hdw" (is "~(\\E x : ?z_hed(x))")
 by (unfold z_Hdw_z_Hdv, fact z_Hdv)
 have z_Hee: "?z_hbz(voteds(a))" (is "_=>?z_hef")
 by (rule zenon_all_0 [of "?z_hbz" "voteds(a)", OF z_Hbr])
 show FALSE
 proof (rule zenon_imply [OF z_Hee])
  assume z_Heg:"(~?z_he)"
  show FALSE
  by (rule notE [OF z_Heg z_He])
 next
  assume z_Hef:"?z_hef"
  have z_Heh_z_Hef: "(\\A x:((x \\in voteds(a))=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))&((x[''bal'']) <= (a_r2a[''bal'']))))))) == ?z_hef" (is "?z_heh == _")
  by (unfold bAll_def)
  have z_Heh: "?z_heh" (is "\\A x : ?z_hen(x)")
  by (unfold z_Heh_z_Hef, fact z_Hef)
  have z_Heo: "?z_hen((CHOOSE x:(~((x \\in voteds(a))=>bAll(Nat, (\<lambda>a_s2a. (((x[''slot''])=a_s2a)=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((a_r2a[''slot''])=a_s2a)&((x[''bal'']) <= (a_r2a[''bal'']))))))))))))" (is "_=>?z_hep")
  by (rule zenon_all_0 [of "?z_hen" "(CHOOSE x:(~((x \\in voteds(a))=>bAll(Nat, (\<lambda>a_s2a. (((x[''slot''])=a_s2a)=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((a_r2a[''slot''])=a_s2a)&((x[''bal'']) <= (a_r2a[''bal''])))))))))))", OF z_Heh])
  show FALSE
  proof (rule zenon_imply [OF z_Heo])
   assume z_Heq:"(~?z_hcu)"
   show FALSE
   by (rule notE [OF z_Heq z_Hcu])
  next
   assume z_Hep:"?z_hep"
   have z_Her_z_Hep: "(\\E x:((x \\in PartialBmax(voteds(a)))&((?z_hdd=(x[''slot'']))&(((CHOOSE x:(~((x \\in voteds(a))=>bAll(Nat, (\<lambda>a_s2a. (((x[''slot''])=a_s2a)=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((a_r2a[''slot''])=a_s2a)&((x[''bal'']) <= (a_r2a[''bal''])))))))))))[''bal'']) <= (x[''bal'']))))) == ?z_hep" (is "?z_her == _")
   by (unfold bEx_def)
   have z_Her: "?z_her" (is "\\E x : ?z_hev(x)")
   by (unfold z_Her_z_Hep, fact z_Hep)
   have z_Hew: "?z_hev((CHOOSE x:((x \\in PartialBmax(voteds(a)))&((?z_hdd=(x[''slot'']))&(((CHOOSE x:(~((x \\in voteds(a))=>bAll(Nat, (\<lambda>a_s2a. (((x[''slot''])=a_s2a)=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((a_r2a[''slot''])=a_s2a)&((x[''bal'']) <= (a_r2a[''bal''])))))))))))[''bal'']) <= (x[''bal'']))))))" (is "?z_hey&?z_hez")
   by (rule zenon_ex_choose_0 [of "?z_hev", OF z_Her])
   have z_Hey: "?z_hey"
   by (rule zenon_and_0 [OF z_Hew])
   have z_Hez: "?z_hez" (is "?z_hfa&?z_hfb")
   by (rule zenon_and_1 [OF z_Hew])
   have z_Hfa: "?z_hfa" (is "_=?z_hfc")
   by (rule zenon_and_0 [OF z_Hez])
   have z_Hfb: "?z_hfb"
   by (rule zenon_and_1 [OF z_Hez])
   have z_Hfd: "~?z_hed((CHOOSE x:((x \\in PartialBmax(voteds(a)))&((?z_hdd=(x[''slot'']))&(((CHOOSE x:(~((x \\in voteds(a))=>bAll(Nat, (\<lambda>a_s2a. (((x[''slot''])=a_s2a)=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((a_r2a[''slot''])=a_s2a)&((x[''bal'']) <= (a_r2a[''bal''])))))))))))[''bal'']) <= (x[''bal'']))))))" (is "~(_&?z_hfe)")
   by (rule zenon_notex_0 [of "?z_hed" "(CHOOSE x:((x \\in PartialBmax(voteds(a)))&((?z_hdd=(x[''slot'']))&(((CHOOSE x:(~((x \\in voteds(a))=>bAll(Nat, (\<lambda>a_s2a. (((x[''slot''])=a_s2a)=>bEx(PartialBmax(voteds(a)), (\<lambda>a_r2a. (((a_r2a[''slot''])=a_s2a)&((x[''bal'']) <= (a_r2a[''bal''])))))))))))[''bal'']) <= (x[''bal''])))))", OF z_Hdw])
   show FALSE
   proof (rule zenon_notand [OF z_Hfd])
    assume z_Hff:"(~?z_hey)"
    show FALSE
    by (rule notE [OF z_Hff z_Hey])
   next
    assume z_Hfg:"(~?z_hfe)" (is "~(?z_hfh&_)")
    show FALSE
    proof (rule zenon_notand [OF z_Hfg])
     assume z_Hfi:"(?z_hfc~=?z_hdp)"
     show FALSE
     proof (rule notE [OF z_Hfi])
      have z_Hfh: "?z_hfh"
      by (rule subst [where P="(\<lambda>zenon_Vaq. (zenon_Vaq=?z_hdp))", OF z_Hfa], fact z_Hdt)
      thus "?z_hfh" .
     qed
    next
     assume z_Hfm:"(~?z_hfb)"
     show FALSE
     by (rule notE [OF z_Hfm z_Hfb])
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 35"; *} qed
lemma ob'104:
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Acceptors
fixes Values
fixes Quorums
fixes Proposers
fixes sent sent'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition PartialBmax suppressed *)
(* usable definition voteds suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Bmax suppressed *)
(* usable definition FreeSlots suppressed *)
(* usable definition NewProposals suppressed *)
(* usable definition ProposeDecrees suppressed *)
(* usable definition VS suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Preempt suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
assumes v'64: "(((TypeOK) \<and> (MsgInv)))"
assumes v'65: "(((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))"
assumes v'70: "(((Next) \<Longrightarrow> ((((a_hef12f5554781c2213604492856f635a :: c)) \<and> ((a_h40eb8e4076bde0f0cc5367a8972679a :: c))))))"
assumes v'71: "((((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars))) \<Longrightarrow> ((((a_hef12f5554781c2213604492856f635a :: c)) \<and> ((a_h40eb8e4076bde0f0cc5367a8972679a :: c))))))"
shows "((((a_hef12f5554781c2213604492856f635a :: c)) \<and> ((a_h40eb8e4076bde0f0cc5367a8972679a :: c))))"(is "PROP ?ob'104")
proof -
ML_command {* writeln "*** TLAPS ENTER 104"; *}
show "PROP ?ob'104"

(* BEGIN ZENON INPUT
;; file=MultiPaxosUs.tlaps/tlapm_a75371.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >MultiPaxosUs.tlaps/tlapm_a75371.znn.out
;; obligation #104
$hyp "v'64" (/\ TypeOK MsgInv)
$hyp "v'65" (\/ Next (= a_h4fd5f73954dc53af536c1c75068837a
vars))
$hyp "v'70" (=> Next (/\ a_hef12f5554781c2213604492856f635a
a_h40eb8e4076bde0f0cc5367a8972679a))
$hyp "v'71" (=> (= a_h4fd5f73954dc53af536c1c75068837a
vars) (/\ a_hef12f5554781c2213604492856f635a
a_h40eb8e4076bde0f0cc5367a8972679a))
$goal (/\ a_hef12f5554781c2213604492856f635a
a_h40eb8e4076bde0f0cc5367a8972679a)
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hb:"(Next|(a_h4fd5f73954dc53af536c1c75068837a=vars))" (is "_|?z_hg")
 using v'65 by blast
 have z_Hd:"(?z_hg=>(a_hef12f5554781c2213604492856f635a&a_h40eb8e4076bde0f0cc5367a8972679a))" (is "_=>?z_hj")
 using v'71 by blast
 have z_Hc:"(Next=>?z_hj)"
 using v'70 by blast
 assume z_He:"(~?z_hj)"
 show FALSE
 proof (rule zenon_or [OF z_Hb])
  assume z_Hf:"Next"
  show FALSE
  proof (rule zenon_imply [OF z_Hc])
   assume z_Hm:"(~Next)"
   show FALSE
   by (rule notE [OF z_Hm z_Hf])
  next
   assume z_Hj:"?z_hj"
   show FALSE
   by (rule notE [OF z_He z_Hj])
  qed
 next
  assume z_Hg:"?z_hg"
  show FALSE
  proof (rule zenon_imply [OF z_Hd])
   assume z_Hn:"(a_h4fd5f73954dc53af536c1c75068837a~=vars)"
   show FALSE
   by (rule notE [OF z_Hn z_Hg])
  next
   assume z_Hj:"?z_hj"
   show FALSE
   by (rule notE [OF z_He z_Hj])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 104"; *} qed
lemma ob'128:
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Acceptors
fixes Values
fixes Quorums
fixes Proposers
fixes sent sent'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition PartialBmax suppressed *)
(* usable definition voteds suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Bmax suppressed *)
(* usable definition FreeSlots suppressed *)
(* usable definition NewProposals suppressed *)
(* usable definition ProposeDecrees suppressed *)
(* usable definition VS suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Preempt suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
assumes v'63: "(((TypeOK) \<and> (MsgInv)))"
assumes v'64: "(((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))"
fixes p
assumes p_in : "(p \<in> (Proposers))"
assumes v'79: "(\<exists> b \<in> (Nat) : (((~ (\<exists> m \<in> (sent) : (((((fapply ((m), (''type''))) = (''2a''))) \<and> (((fapply ((m), (''bal''))) = (b)))))))) & (\<exists> Q \<in> (Quorums) : (\<exists> S \<in> ((SUBSET (subsetOf((sent), %m. (((((fapply ((m), (''type''))) = (''1b''))) \<and> (((fapply ((m), (''bal''))) = (b))))))))) : ((\<forall> a \<in> (Q) : (\<exists> m \<in> (S) : (((fapply ((m), (''from''))) = (a))))) & ((Send (({(((''type'' :> (''2a'')) @@ (''from'' :> (p)) @@ (''bal'' :> (b)) @@ (''decrees'' :> ((ProposeDecrees (((VS ((S), (Q))))))))))})))))))))"
shows "(\<exists> b \<in> (Nat) : (\<exists> Q \<in> (Quorums) : (\<exists> S \<in> ((SUBSET (sent))) : ((((S) \<in> ((SUBSET (subsetOf((sent), %m. (((((fapply ((m), (''type''))) = (''1b''))) \<and> (((fapply ((m), (''bal''))) = (b))))))))))) & (\<forall> a \<in> (Q) : (\<exists> m \<in> (S) : (((fapply ((m), (''from''))) = (a))))) & ((Send (({(((''type'' :> (''2a'')) @@ (''from'' :> (p)) @@ (''bal'' :> (b)) @@ (''decrees'' :> ((ProposeDecrees (((VS ((S), (Q))))))))))}))))))))"(is "PROP ?ob'128")
proof -
ML_command {* writeln "*** TLAPS ENTER 128"; *}
show "PROP ?ob'128"

(* BEGIN ZENON INPUT
;; file=MultiPaxosUs.tlaps/tlapm_d229aa.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >MultiPaxosUs.tlaps/tlapm_d229aa.znn.out
;; obligation #128
$hyp "v'63" (/\ TypeOK MsgInv)
$hyp "v'64" (\/ Next (= a_h4fd5f73954dc53af536c1c75068837a
vars))
$hyp "p_in" (TLA.in p Proposers)
$hyp "v'79" (TLA.bEx arith.N ((b) (/\ (-. (TLA.bEx sent ((m) (/\ (= (TLA.fapply m "type")
"2a") (= (TLA.fapply m "bal") b)))))
(TLA.bEx Quorums ((Q) (TLA.bEx (TLA.SUBSET (TLA.subsetOf sent ((m) (/\ (= (TLA.fapply m "type")
"1b") (= (TLA.fapply m "bal")
b))))) ((S) (/\ (TLA.bAll Q ((a) (TLA.bEx S ((m) (= (TLA.fapply m "from")
a)))))
(Send (TLA.set (TLA.record "type" "2a" "from" p "bal" b "decrees" (ProposeDecrees (VS S
Q)))))))))))))
$goal (TLA.bEx arith.N ((b) (TLA.bEx Quorums ((Q) (TLA.bEx (TLA.SUBSET sent) ((S) (/\ (TLA.in S
(TLA.SUBSET (TLA.subsetOf sent ((m) (/\ (= (TLA.fapply m "type") "1b")
(= (TLA.fapply m "bal") b))))))
(TLA.bAll Q ((a) (TLA.bEx S ((m) (= (TLA.fapply m "from") a)))))
(Send (TLA.set (TLA.record "type" "2a" "from" p "bal" b "decrees" (ProposeDecrees (VS S
Q))))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"bEx(Nat, (\<lambda>b. ((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=b)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=b))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (b) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))" (is "?z_hd")
 using v'79 by blast
 assume z_He:"(~bEx(Nat, (\<lambda>b. bEx(Quorums, (\<lambda>Q. bEx(SUBSET(sent), (\<lambda>S. ((S \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=b))))))&(bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (b) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))}))))))))))" (is "~?z_hbz")
 have z_Hci_z_Hd: "(\\E x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))}))))))))) == ?z_hd" (is "?z_hci == _")
 by (unfold bEx_def)
 have z_Hci: "?z_hci" (is "\\E x : ?z_hde(x)")
 by (unfold z_Hci_z_Hd, fact z_Hd)
 have z_Hdf: "?z_hde((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))}))))))))))" (is "?z_hdh&?z_hdi")
 by (rule zenon_ex_choose_0 [of "?z_hde", OF z_Hci])
 have z_Hdh: "?z_hdh"
 by (rule zenon_and_0 [OF z_Hdf])
 have z_Hdi: "?z_hdi" (is "?z_hdj&?z_hdk")
 by (rule zenon_and_1 [OF z_Hdf])
 have z_Hdk: "?z_hdk"
 by (rule zenon_and_1 [OF z_Hdi])
 have z_Hdl_z_Hdk: "(\\E x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))) == ?z_hdk" (is "?z_hdl == _")
 by (unfold bEx_def)
 have z_Hdl: "?z_hdl" (is "\\E x : ?z_hec(x)")
 by (unfold z_Hdl_z_Hdk, fact z_Hdk)
 have z_Hed: "?z_hec((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))))" (is "?z_hef&?z_heg")
 by (rule zenon_ex_choose_0 [of "?z_hec", OF z_Hdl])
 have z_Hef: "?z_hef"
 by (rule zenon_and_0 [OF z_Hed])
 have z_Heg: "?z_heg"
 by (rule zenon_and_1 [OF z_Hed])
 have z_Heh_z_Heg: "(\\E x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))) == ?z_heg" (is "?z_heh == _")
 by (unfold bEx_def)
 have z_Heh: "?z_heh" (is "\\E x : ?z_het(x)")
 by (unfold z_Heh_z_Heg, fact z_Heg)
 have z_Heu: "?z_het((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))" (is "?z_hew&?z_hex")
 by (rule zenon_ex_choose_0 [of "?z_het", OF z_Heh])
 have z_Hew: "?z_hew"
 by (rule zenon_and_0 [OF z_Heu])
 have z_Hex: "?z_hex" (is "?z_hey&?z_hez")
 by (rule zenon_and_1 [OF z_Heu])
 have z_Hey: "?z_hey"
 by (rule zenon_and_0 [OF z_Hex])
 have z_Hez: "?z_hez"
 by (rule zenon_and_1 [OF z_Hex])
 have z_Hfa: "((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))) \\subseteq subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))}))))))))))))))" (is "?z_hfa")
 by (rule zenon_in_SUBSET_0 [of "(CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))}))))" "subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))", OF z_Hew])
 have z_Hfb_z_Hfa: "bAll((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))), (\<lambda>x. (x \\in subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))) == ?z_hfa" (is "?z_hfb == _")
 by (unfold subset_def)
 have z_Hfb: "?z_hfb"
 by (unfold z_Hfb_z_Hfa, fact z_Hfa)
 have z_Hfe_z_Hfb: "(\\A x:((x \\in (CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))=>(x \\in subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))) == ?z_hfb" (is "?z_hfe == _")
 by (unfold bAll_def)
 have z_Hfe: "?z_hfe" (is "\\A x : ?z_hfh(x)")
 by (unfold z_Hfe_z_Hfb, fact z_Hfb)
 have z_Hfi_z_He: "(~(\\E x:((x \\in Nat)&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(sent), (\<lambda>S. ((S \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))))&(bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) == (~?z_hbz)" (is "?z_hfi == ?z_he")
 by (unfold bEx_def)
 have z_Hfi: "?z_hfi" (is "~(\\E x : ?z_hfr(x))")
 by (unfold z_Hfi_z_He, fact z_He)
 have z_Hfs: "~?z_hfr((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))}))))))))))" (is "~(_&?z_hft)")
 by (rule zenon_notex_0 [of "?z_hfr" "(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))", OF z_Hfi])
 show FALSE
 proof (rule zenon_notand [OF z_Hfs])
  assume z_Hfu:"(~?z_hdh)"
  show FALSE
  by (rule notE [OF z_Hfu z_Hdh])
 next
  assume z_Hfv:"(~?z_hft)"
  have z_Hfw_z_Hfv: "(~(\\E x:((x \\in Quorums)&bEx(SUBSET(sent), (\<lambda>S. ((S \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))))) == (~?z_hft)" (is "?z_hfw == ?z_hfv")
  by (unfold bEx_def)
  have z_Hfw: "?z_hfw" (is "~(\\E x : ?z_hgd(x))")
  by (unfold z_Hfw_z_Hfv, fact z_Hfv)
  have z_Hge: "~?z_hgd((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))))" (is "~(_&?z_hgf)")
  by (rule zenon_notex_0 [of "?z_hgd" "(CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))", OF z_Hfw])
  show FALSE
  proof (rule zenon_notand [OF z_Hge])
   assume z_Hgg:"(~?z_hef)"
   show FALSE
   by (rule notE [OF z_Hgg z_Hef])
  next
   assume z_Hgh:"(~?z_hgf)"
   have z_Hgi_z_Hgh: "(~(\\E x:((x \\in SUBSET(sent))&((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))) == (~?z_hgf)" (is "?z_hgi == ?z_hgh")
   by (unfold bEx_def)
   have z_Hgi: "?z_hgi" (is "~(\\E x : ?z_hgm(x))")
   by (unfold z_Hgi_z_Hgh, fact z_Hgh)
   have z_Hgn: "~?z_hgm((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))" (is "~(?z_hgo&?z_heu)")
   by (rule zenon_notex_0 [of "?z_hgm" "(CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))}))))", OF z_Hgi])
   show FALSE
   proof (rule zenon_notand [OF z_Hgn])
    assume z_Hgp:"(~?z_hgo)"
    have z_Hgq: "(~((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))) \\subseteq sent))" (is "~?z_hgr")
    by (rule zenon_notin_SUBSET_0 [of "(CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))}))))" "sent", OF z_Hgp])
    have z_Hgs_z_Hgq: "(~bAll((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))), (\<lambda>zenon_Vib. (zenon_Vib \\in sent)))) == (~?z_hgr)" (is "?z_hgs == ?z_hgq")
    by (unfold subset_def)
    have z_Hgs: "?z_hgs" (is "~?z_hgt")
    by (unfold z_Hgs_z_Hgq, fact z_Hgq)
    have z_Hgx_z_Hgs: "(~(\\A x:((x \\in (CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))=>(x \\in sent)))) == ?z_hgs" (is "?z_hgx == _")
    by (unfold bAll_def)
    have z_Hgx: "?z_hgx" (is "~(\\A x : ?z_hhb(x))")
    by (unfold z_Hgx_z_Hgs, fact z_Hgs)
    have z_Hhc: "(\\E x:(~((x \\in (CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))=>(x \\in sent))))" (is "\\E x : ?z_hhe(x)")
    by (rule zenon_notallex_0 [of "?z_hhb", OF z_Hgx])
    have z_Hhf: "?z_hhe((CHOOSE x:(~((x \\in (CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))=>(x \\in sent)))))" (is "~(?z_hhh=>?z_hhi)")
    by (rule zenon_ex_choose_0 [of "?z_hhe", OF z_Hhc])
    have z_Hhh: "?z_hhh"
    by (rule zenon_notimply_0 [OF z_Hhf])
    have z_Hhj: "(~?z_hhi)"
    by (rule zenon_notimply_1 [OF z_Hhf])
    have z_Hhk: "?z_hfh((CHOOSE x:(~((x \\in (CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))=>(x \\in sent)))))" (is "_=>?z_hhl")
    by (rule zenon_all_0 [of "?z_hfh" "(CHOOSE x:(~((x \\in (CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))=>(x \\in sent))))", OF z_Hfe])
    show FALSE
    proof (rule zenon_imply [OF z_Hhk])
     assume z_Hhm:"(~?z_hhh)"
     show FALSE
     by (rule notE [OF z_Hhm z_Hhh])
    next
     assume z_Hhl:"?z_hhl"
     have z_Hhi: "?z_hhi"
     by (rule zenon_in_subsetof_0 [of "(CHOOSE x:(~((x \\in (CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))=>(x \\in sent))))" "sent" "(\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))}))))))))))))", OF z_Hhl])
     show FALSE
     by (rule notE [OF z_Hhj z_Hhi])
    qed
   next
    assume z_Hhn:"(~?z_heu)"
    show FALSE
    proof (rule zenon_notand [OF z_Hhn])
     assume z_Hho:"(~?z_hew)"
     show FALSE
     by (rule notE [OF z_Hho z_Hew])
    next
     assume z_Hhp:"(~?z_hex)"
     show FALSE
     proof (rule zenon_notand [OF z_Hhp])
      assume z_Hhq:"(~?z_hey)"
      show FALSE
      by (rule notE [OF z_Hhq z_Hey])
     next
      assume z_Hhr:"(~?z_hez)"
      show FALSE
      by (rule notE [OF z_Hhr z_Hez])
     qed
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 128"; *} qed
lemma ob'149:
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Acceptors
fixes Values
fixes Quorums
fixes Proposers
fixes sent sent'
(* usable definition vars suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition PartialBmax suppressed *)
(* usable definition voteds suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Bmax suppressed *)
(* usable definition FreeSlots suppressed *)
(* usable definition NewProposals suppressed *)
(* usable definition ProposeDecrees suppressed *)
(* usable definition VS suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Preempt suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
assumes v'62: "(((((sent) \<in> ((SUBSET (Messages))))) \<and> (MsgInv)))"
assumes v'63: "(((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))"
fixes a
assumes a_in : "(a \<in> (Acceptors))"
fixes m
assumes m_in : "(m \<in> (sent))"
assumes v'84: "(\<forall> a_m2a \<in> (subsetOf((sent), %m_1. (((((fapply ((m_1), (''type''))) \<in> ({(''1b''), (''2b'')}))) \<and> (((fapply ((m_1), (''from''))) = (a))))))) : ((greater ((fapply ((m), (''bal''))), (fapply ((a_m2a), (''bal'')))))))"
assumes v'85: "(((fapply ((m), (''type''))) = (''1a'')))"
assumes v'86: "((((a_senthash_primea :: c)) = (((sent) \<union> ({(((''type'' :> (''1b'')) @@ (''from'' :> (a)) @@ (''bal'' :> (fapply ((m), (''bal'')))) @@ (''voted'' :> ((PartialBmax (((voteds ((a))))))))))})))))"
assumes v'87: "((({(((''type'' :> (''1b'')) @@ (''from'' :> (a)) @@ (''bal'' :> (fapply ((m), (''bal'')))) @@ (''voted'' :> ((PartialBmax (((voteds ((a))))))))))}) \<subseteq> (Messages)))"
shows "((((a_senthash_primea :: c)) \<in> ((SUBSET (Messages)))))"(is "PROP ?ob'149")
proof -
ML_command {* writeln "*** TLAPS ENTER 149"; *}
show "PROP ?ob'149"

(* BEGIN ZENON INPUT
;; file=MultiPaxosUs.tlaps/tlapm_d24897.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >MultiPaxosUs.tlaps/tlapm_d24897.znn.out
;; obligation #149
$hyp "v'62" (/\ (TLA.in sent (TLA.SUBSET Messages))
MsgInv)
$hyp "v'63" (\/ Next (= a_h4fd5f73954dc53af536c1c75068837a
vars))
$hyp "a_in" (TLA.in a Acceptors)
$hyp "m_in" (TLA.in m sent)
$hyp "v'84" (TLA.bAll (TLA.subsetOf sent ((m_1) (/\ (TLA.in (TLA.fapply m_1 "type")
(TLA.set "1b" "2b")) (= (TLA.fapply m_1 "from")
a)))) ((a_m2a) (arith.lt (TLA.fapply a_m2a "bal")
(TLA.fapply m "bal"))))
$hyp "v'85" (= (TLA.fapply m "type") "1a")
$hyp "v'86" (= a_senthash_primea (TLA.cup sent
(TLA.set (TLA.record "type" "1b" "from" a "bal" (TLA.fapply m "bal") "voted" (PartialBmax (voteds a))))))
$hyp "v'87" (TLA.subseteq (TLA.set (TLA.record "type" "1b" "from" a "bal" (TLA.fapply m "bal") "voted" (PartialBmax (voteds a))))
Messages)
$goal (TLA.in a_senthash_primea
(TLA.SUBSET Messages))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hg:"(a_senthash_primea=(sent \\cup {(''type'' :> (''1b'') @@ ''from'' :> (a) @@ ''bal'' :> ((m[''bal''])) @@ ''voted'' :> (PartialBmax(voteds(a))))}))" (is "_=?z_hk")
 using v'86 by blast
 have z_Ha:"((sent \\in SUBSET(Messages))&MsgInv)" (is "?z_hy&_")
 using v'62 by blast
 have z_Hh:"({(''type'' :> (''1b'') @@ ''from'' :> (a) @@ ''bal'' :> ((m[''bal''])) @@ ''voted'' :> (PartialBmax(voteds(a))))} \\subseteq Messages)" (is "?z_hh")
 using v'87 by blast
 assume z_Hi:"(~(a_senthash_primea \\in SUBSET(Messages)))" (is "~?z_hbc")
 have z_Hy: "?z_hy"
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hbd: "(sent \\subseteq Messages)" (is "?z_hbd")
 by (rule zenon_in_SUBSET_0 [of "sent" "Messages", OF z_Hy])
 have z_Hbe: "(~(a_senthash_primea \\subseteq Messages))" (is "~?z_hbf")
 by (rule zenon_notin_SUBSET_0 [of "a_senthash_primea" "Messages", OF z_Hi])
 have z_Hbg: "(~(?z_hk \\subseteq Messages))" (is "~?z_hbh")
 by (rule subst [where P="(\<lambda>zenon_Vz. (~(zenon_Vz \\subseteq Messages)))", OF z_Hg z_Hbe])
 show FALSE
 proof (rule zenon_not_cup_subseteq [of , OF z_Hbg])
  assume z_Hbm:"(~?z_hbd)"
  show FALSE
  by (rule notE [OF z_Hbm z_Hbd])
 next
  assume z_Hbn:"(~?z_hh)"
  show FALSE
  by (rule notE [OF z_Hbn z_Hh])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 149"; *} qed
lemma ob'143:
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Acceptors
fixes Values
fixes Quorums
fixes Proposers
fixes sent sent'
(* usable definition vars suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition PartialBmax suppressed *)
(* usable definition voteds suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Bmax suppressed *)
(* usable definition FreeSlots suppressed *)
(* usable definition NewProposals suppressed *)
(* usable definition ProposeDecrees suppressed *)
(* usable definition VS suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Preempt suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
assumes v'60: "(((((sent) \<in> ((SUBSET ((((((((([''type'' : ({(''1a'')}), ''bal'' : (Nat), ''from'' : (Proposers)]) \<union> ([''type'' : ({(''1b'')}), ''bal'' : (Nat), ''voted'' : ((SUBSET ([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)]))), ''from'' : (Acceptors)]))) \<union> ([''type'' : ({(''2a'')}), ''bal'' : (Nat), ''decrees'' : ((SUBSET ([''slot'' : (Nat), ''val'' : (Values)]))), ''from'' : (Proposers)]))) \<union> ([''type'' : ({(''2b'')}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]))) \<union> ([''type'' : ({(''preempt'')}), ''to'' : (Proposers), ''bal'' : (Nat)]))))))) \<and> (MsgInv)))"
assumes v'61: "(((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))"
fixes p
assumes p_in : "(p \<in> (Proposers))"
fixes b
assumes b_in : "(b \<in> (Nat))"
fixes Q
assumes Q_in : "(Q \<in> (Quorums))"
fixes S
assumes S_in : "(S \<in> ((SUBSET (sent))))"
assumes v'88: "(\<exists> b_1 \<in> (Nat) : (((~ (\<exists> m \<in> (sent) : (((((fapply ((m), (''type''))) = (''2a''))) \<and> (((fapply ((m), (''bal''))) = (b_1)))))))) & (\<exists> Q_1 \<in> (Quorums) : (\<exists> S_1 \<in> ((SUBSET (subsetOf((sent), %m. (((((fapply ((m), (''type''))) = (''1b''))) \<and> (((fapply ((m), (''bal''))) = (b_1))))))))) : ((\<forall> a \<in> (Q_1) : (\<exists> m \<in> (S_1) : (((fapply ((m), (''from''))) = (a))))) & ((((a_senthash_primea :: c)) = (((sent) \<union> ({(((''type'' :> (''2a'')) @@ (''from'' :> (p)) @@ (''bal'' :> (b_1)) @@ (''decrees'' :> ((ProposeDecrees (((VS ((S_1), (Q_1))))))))))}))))))))))"
assumes v'89: "(\<forall> a_m2a \<in> ((((a_senthash_primea :: c)) \\ (sent))) : ((((((((fapply ((a_m2a), (''type''))) = (''2a''))) \<and> (((fapply ((a_m2a), (''from''))) = (p))))) \<and> (((fapply ((a_m2a), (''bal''))) = (b))))) & (((fapply ((a_m2a), (''decrees''))) = ((ProposeDecrees (((VS ((S), (Q)))))))))))"
assumes v'90: "((((S) \<in> ((SUBSET (subsetOf((sent), %m. (((((fapply ((m), (''type''))) = (''1b''))) \<and> (((fapply ((m), (''bal''))) = (b))))))))))) & (\<forall> a \<in> (Q) : (\<exists> m \<in> (S) : (((fapply ((m), (''from''))) = (a))))))"
assumes v'91: "((((a_senthash_primea :: c)) = (((sent) \<union> ({(((''type'' :> (''2a'')) @@ (''from'' :> (p)) @@ (''bal'' :> (b)) @@ (''decrees'' :> ((ProposeDecrees (((VS ((S), (Q))))))))))})))))"
assumes v'92: "((((ProposeDecrees (((VS ((S), (Q))))))) \<subseteq> ([''slot'' : (Nat), ''val'' : (Values)])))"
assumes v'93: "((((((a_senthash_primea :: c)) \\ (sent))) \<subseteq> ((((((((([''type'' : ({(''1a'')}), ''bal'' : (Nat), ''from'' : (Proposers)]) \<union> ([''type'' : ({(''1b'')}), ''bal'' : (Nat), ''voted'' : ((SUBSET ([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)]))), ''from'' : (Acceptors)]))) \<union> ([''type'' : ({(''2a'')}), ''bal'' : (Nat), ''decrees'' : ((SUBSET ([''slot'' : (Nat), ''val'' : (Values)]))), ''from'' : (Proposers)]))) \<union> ([''type'' : ({(''2b'')}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]))) \<union> ([''type'' : ({(''preempt'')}), ''to'' : (Proposers), ''bal'' : (Nat)])))))"
shows "((((a_senthash_primea :: c)) \<in> ((SUBSET ((((((((([''type'' : ({(''1a'')}), ''bal'' : (Nat), ''from'' : (Proposers)]) \<union> ([''type'' : ({(''1b'')}), ''bal'' : (Nat), ''voted'' : ((SUBSET ([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)]))), ''from'' : (Acceptors)]))) \<union> ([''type'' : ({(''2a'')}), ''bal'' : (Nat), ''decrees'' : ((SUBSET ([''slot'' : (Nat), ''val'' : (Values)]))), ''from'' : (Proposers)]))) \<union> ([''type'' : ({(''2b'')}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]))) \<union> ([''type'' : ({(''preempt'')}), ''to'' : (Proposers), ''bal'' : (Nat)])))))))"(is "PROP ?ob'143")
proof -
ML_command {* writeln "*** TLAPS ENTER 143"; *}
show "PROP ?ob'143"

(* BEGIN ZENON INPUT
;; file=MultiPaxosUs.tlaps/tlapm_665dfc.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >MultiPaxosUs.tlaps/tlapm_665dfc.znn.out
;; obligation #143
$hyp "v'60" (/\ (TLA.in sent
(TLA.SUBSET (TLA.cup (TLA.cup (TLA.cup (TLA.cup (TLA.recordset "type" (TLA.set "1a") "bal" arith.N "from" Proposers)
(TLA.recordset "type" (TLA.set "1b") "bal" arith.N "voted" (TLA.SUBSET (TLA.recordset "bal" arith.N "slot" arith.N "val" Values)) "from" Acceptors))
(TLA.recordset "type" (TLA.set "2a") "bal" arith.N "decrees" (TLA.SUBSET (TLA.recordset "slot" arith.N "val" Values)) "from" Proposers))
(TLA.recordset "type" (TLA.set "2b") "bal" arith.N "slot" arith.N "val" Values "from" Acceptors))
(TLA.recordset "type" (TLA.set "preempt") "to" Proposers "bal" arith.N))))
MsgInv)
$hyp "v'61" (\/ Next (= a_h4fd5f73954dc53af536c1c75068837a
vars))
$hyp "p_in" (TLA.in p Proposers)
$hyp "b_in" (TLA.in b arith.N)
$hyp "Q_in" (TLA.in Q Quorums)
$hyp "S_in" (TLA.in S (TLA.SUBSET sent))
$hyp "v'88" (TLA.bEx arith.N ((b_1) (/\ (-. (TLA.bEx sent ((m) (/\ (= (TLA.fapply m "type")
"2a") (= (TLA.fapply m "bal") b_1)))))
(TLA.bEx Quorums ((Q_1) (TLA.bEx (TLA.SUBSET (TLA.subsetOf sent ((m) (/\ (= (TLA.fapply m "type")
"1b") (= (TLA.fapply m "bal")
b_1))))) ((S_1) (/\ (TLA.bAll Q_1 ((a) (TLA.bEx S_1 ((m) (= (TLA.fapply m "from")
a))))) (= a_senthash_primea (TLA.cup sent
(TLA.set (TLA.record "type" "2a" "from" p "bal" b_1 "decrees" (ProposeDecrees (VS S_1
Q_1))))))))))))))
$hyp "v'89" (TLA.bAll (TLA.setminus a_senthash_primea
sent) ((a_m2a) (/\ (/\ (/\ (= (TLA.fapply a_m2a "type") "2a")
(= (TLA.fapply a_m2a "from") p)) (= (TLA.fapply a_m2a "bal") b))
(= (TLA.fapply a_m2a "decrees") (ProposeDecrees (VS S
Q))))))
$hyp "v'90" (/\ (TLA.in S
(TLA.SUBSET (TLA.subsetOf sent ((m) (/\ (= (TLA.fapply m "type") "1b")
(= (TLA.fapply m "bal") b))))))
(TLA.bAll Q ((a) (TLA.bEx S ((m) (= (TLA.fapply m "from")
a))))))
$hyp "v'91" (= a_senthash_primea (TLA.cup sent
(TLA.set (TLA.record "type" "2a" "from" p "bal" b "decrees" (ProposeDecrees (VS S
Q))))))
$hyp "v'92" (TLA.subseteq (ProposeDecrees (VS S Q))
(TLA.recordset "slot" arith.N "val" Values))
$hyp "v'93" (TLA.subseteq (TLA.setminus a_senthash_primea sent)
(TLA.cup (TLA.cup (TLA.cup (TLA.cup (TLA.recordset "type" (TLA.set "1a") "bal" arith.N "from" Proposers)
(TLA.recordset "type" (TLA.set "1b") "bal" arith.N "voted" (TLA.SUBSET (TLA.recordset "bal" arith.N "slot" arith.N "val" Values)) "from" Acceptors))
(TLA.recordset "type" (TLA.set "2a") "bal" arith.N "decrees" (TLA.SUBSET (TLA.recordset "slot" arith.N "val" Values)) "from" Proposers))
(TLA.recordset "type" (TLA.set "2b") "bal" arith.N "slot" arith.N "val" Values "from" Acceptors))
(TLA.recordset "type" (TLA.set "preempt") "to" Proposers "bal" arith.N)))
$goal (TLA.in a_senthash_primea
(TLA.SUBSET (TLA.cup (TLA.cup (TLA.cup (TLA.cup (TLA.recordset "type" (TLA.set "1a") "bal" arith.N "from" Proposers)
(TLA.recordset "type" (TLA.set "1b") "bal" arith.N "voted" (TLA.SUBSET (TLA.recordset "bal" arith.N "slot" arith.N "val" Values)) "from" Acceptors))
(TLA.recordset "type" (TLA.set "2a") "bal" arith.N "decrees" (TLA.SUBSET (TLA.recordset "slot" arith.N "val" Values)) "from" Proposers))
(TLA.recordset "type" (TLA.set "2b") "bal" arith.N "slot" arith.N "val" Values "from" Acceptors))
(TLA.recordset "type" (TLA.set "preempt") "to" Proposers "bal" arith.N))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hj:"(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (b) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))}))" (is "_=?z_ho")
 using v'91 by blast
 have z_Ha:"((sent \\in SUBSET((((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)])))&MsgInv)" (is "?z_hbd&_")
 using v'60 by blast
 have z_Hg:"bEx(Nat, (\<lambda>b_1. ((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=b_1)))))&bEx(Quorums, (\<lambda>Q_1. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=b_1))))), (\<lambda>S_1. (bAll(Q_1, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (b_1) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, Q_1))))}))))))))))" (is "?z_hg")
 using v'88 by blast
 have z_Hl:"((a_senthash_primea \\ sent) \\subseteq (((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)]))" (is "?z_hl")
 using v'93 by blast
 assume z_Hm:"(~(a_senthash_primea \\in SUBSET((((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)]))))" (is "~?z_hdx")
 have z_Hbd: "?z_hbd"
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hdy: "(sent \\subseteq (((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)]))" (is "?z_hdy")
 by (rule zenon_in_SUBSET_0 [of "sent" "(((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)])", OF z_Hbd])
 have z_Hdz_z_Hdy: "bAll(sent, (\<lambda>x. (x \\in (((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)])))) == ?z_hdy" (is "?z_hdz == _")
 by (unfold subset_def)
 have z_Hdz: "?z_hdz"
 by (unfold z_Hdz_z_Hdy, fact z_Hdy)
 have z_Hed_z_Hdz: "(\\A x:((x \\in sent)=>(x \\in (((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)])))) == ?z_hdz" (is "?z_hed == _")
 by (unfold bAll_def)
 have z_Hed: "?z_hed" (is "\\A x : ?z_heg(x)")
 by (unfold z_Hed_z_Hdz, fact z_Hdz)
 have z_Heh_z_Hg: "(\\E x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q_1. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S_1. (bAll(Q_1, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, Q_1))))})))))))))) == ?z_hg" (is "?z_heh == _")
 by (unfold bEx_def)
 have z_Heh: "?z_heh" (is "\\E x : ?z_hfd(x)")
 by (unfold z_Heh_z_Hg, fact z_Hg)
 have z_Hfe: "?z_hfd((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q_1. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S_1. (bAll(Q_1, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, Q_1))))})))))))))))" (is "?z_hfg&?z_hfh")
 by (rule zenon_ex_choose_0 [of "?z_hfd", OF z_Heh])
 have z_Hfh: "?z_hfh" (is "?z_hfi&?z_hfj")
 by (rule zenon_and_1 [OF z_Hfe])
 have z_Hfj: "?z_hfj"
 by (rule zenon_and_1 [OF z_Hfh])
 have z_Hfk_z_Hfj: "(\\E x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q_1. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S_1. (bAll(Q_1, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, Q_1))))}))))))))))))))), (\<lambda>S_1. (bAll(x, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q_1. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S_1. (bAll(Q_1, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, Q_1))))}))))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, x))))}))))))) == ?z_hfj" (is "?z_hfk == _")
 by (unfold bEx_def)
 have z_Hfk: "?z_hfk" (is "\\E x : ?z_hgc(x)")
 by (unfold z_Hfk_z_Hfj, fact z_Hfj)
 have z_Hgd: "?z_hgc((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q_1. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S_1. (bAll(Q_1, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, Q_1))))}))))))))))))))), (\<lambda>S_1. (bAll(x, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q_1. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S_1. (bAll(Q_1, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, Q_1))))}))))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, x))))}))))))))" (is "?z_hgf&?z_hgg")
 by (rule zenon_ex_choose_0 [of "?z_hgc", OF z_Hfk])
 have z_Hgg: "?z_hgg"
 by (rule zenon_and_1 [OF z_Hgd])
 have z_Hgh_z_Hgg: "(\\E x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q_1. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S_1. (bAll(Q_1, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, Q_1))))}))))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q_1. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S_1. (bAll(Q_1, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, Q_1))))}))))))))))))))), (\<lambda>S_1. (bAll(x, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q_1. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S_1. (bAll(Q_1, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, Q_1))))}))))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, x))))}))))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q_1. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S_1. (bAll(Q_1, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, Q_1))))}))))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q_1. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S_1. (bAll(Q_1, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, Q_1))))}))))))))))))))), (\<lambda>S_1. (bAll(x, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q_1. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S_1. (bAll(Q_1, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, Q_1))))}))))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, x))))})))))))))))}))))) == ?z_hgg" (is "?z_hgh == _")
 by (unfold bEx_def)
 have z_Hgh: "?z_hgh" (is "\\E x : ?z_hgu(x)")
 by (unfold z_Hgh_z_Hgg, fact z_Hgg)
 have z_Hgv: "?z_hgu((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q_1. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S_1. (bAll(Q_1, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, Q_1))))}))))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q_1. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S_1. (bAll(Q_1, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, Q_1))))}))))))))))))))), (\<lambda>S_1. (bAll(x, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q_1. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S_1. (bAll(Q_1, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, Q_1))))}))))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, x))))}))))))), (\<lambda>a. bEx(x, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q_1. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S_1. (bAll(Q_1, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, Q_1))))}))))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q_1. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S_1. (bAll(Q_1, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, Q_1))))}))))))))))))))), (\<lambda>S_1. (bAll(x, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q_1. bEx(SUBSET(subsetOf(sent, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=x))))), (\<lambda>S_1. (bAll(Q_1, (\<lambda>a. bEx(S_1, (\<lambda>m. ((m[''from''])=a)))))&(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, Q_1))))}))))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S_1, x))))})))))))))))}))))))" (is "?z_hgx&?z_hgy")
 by (rule zenon_ex_choose_0 [of "?z_hgu", OF z_Hgh])
 have z_Hgy: "?z_hgy" (is "?z_hgz&?z_hha")
 by (rule zenon_and_1 [OF z_Hgv])
 have z_Hha: "?z_hha" (is "_=?z_hhb")
 by (rule zenon_and_1 [OF z_Hgy])
 have z_Hhc: "(?z_ho=?z_hhb)"
 by (rule subst [where P="(\<lambda>zenon_Vbn. (zenon_Vbn=?z_hhb))", OF z_Hj z_Hha])
 have z_Hhg_z_Hl: "bAll((a_senthash_primea \\ sent), (\<lambda>x. (x \\in (((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)])))) == ?z_hl" (is "?z_hhg == _")
 by (unfold subset_def)
 have z_Hhg: "?z_hhg"
 by (unfold z_Hhg_z_Hl, fact z_Hl)
 have z_Hhh: "(~(a_senthash_primea \\subseteq (((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)])))" (is "~?z_hhi")
 by (rule zenon_notin_SUBSET_0 [of "a_senthash_primea" "(((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)])", OF z_Hm])
 have z_Hhj_z_Hhh: "(~bAll(a_senthash_primea, (\<lambda>x. (x \\in (((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)]))))) == (~?z_hhi)" (is "?z_hhj == ?z_hhh")
 by (unfold subset_def)
 have z_Hhj: "?z_hhj" (is "~?z_hhk")
 by (unfold z_Hhj_z_Hhh, fact z_Hhh)
 have z_Hhl_z_Hhj: "(~(\\A x:((x \\in a_senthash_primea)=>(x \\in (((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)]))))) == ?z_hhj" (is "?z_hhl == _")
 by (unfold bAll_def)
 have z_Hhl: "?z_hhl" (is "~(\\A x : ?z_hhp(x))")
 by (unfold z_Hhl_z_Hhj, fact z_Hhj)
 have z_Hhq: "(\\E x:(~((x \\in a_senthash_primea)=>(x \\in (((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)])))))" (is "\\E x : ?z_hhs(x)")
 by (rule zenon_notallex_0 [of "?z_hhp", OF z_Hhl])
 have z_Hht: "?z_hhs((CHOOSE x:(~((x \\in a_senthash_primea)=>(x \\in (((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)]))))))" (is "~(?z_hhv=>?z_hhw)")
 by (rule zenon_ex_choose_0 [of "?z_hhs", OF z_Hhq])
 have z_Hhv: "?z_hhv"
 by (rule zenon_notimply_0 [OF z_Hht])
 have z_Hhx: "(~?z_hhw)"
 by (rule zenon_notimply_1 [OF z_Hht])
 have z_Hhy: "((CHOOSE x:(~((x \\in a_senthash_primea)=>(x \\in (((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)]))))) \\in ?z_hhb)" (is "?z_hhy")
 by (rule subst [where P="(\<lambda>zenon_Vyb. ((CHOOSE x:(~((x \\in a_senthash_primea)=>(x \\in (((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)]))))) \\in zenon_Vyb))", OF z_Hha z_Hhv])
 have z_Hic: "((CHOOSE x:(~((x \\in a_senthash_primea)=>(x \\in (((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)]))))) \\in ?z_ho)" (is "?z_hic")
 by (rule ssubst [where P="(\<lambda>zenon_Vyb. ((CHOOSE x:(~((x \\in a_senthash_primea)=>(x \\in (((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)]))))) \\in zenon_Vyb))", OF z_Hhc z_Hhy])
 have z_Hid: "bAll((?z_ho \\ sent), (\<lambda>x. (x \\in (((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)]))))" (is "?z_hid")
 by (rule subst [where P="(\<lambda>zenon_Vdn. bAll((zenon_Vdn \\ sent), (\<lambda>x. (x \\in (((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)])))))", OF z_Hj z_Hhg])
 have z_Hij_z_Hid: "(\\A x:((x \\in (?z_ho \\ sent))=>(x \\in (((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)])))) == ?z_hid" (is "?z_hij == _")
 by (unfold bAll_def)
 have z_Hij: "?z_hij" (is "\\A x : ?z_him(x)")
 by (unfold z_Hij_z_Hid, fact z_Hid)
 have z_Hin: "?z_heg((CHOOSE x:(~((x \\in a_senthash_primea)=>(x \\in (((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)]))))))" (is "?z_hio=>_")
 by (rule zenon_all_0 [of "?z_heg" "(CHOOSE x:(~((x \\in a_senthash_primea)=>(x \\in (((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)])))))", OF z_Hed])
 show FALSE
 proof (rule zenon_imply [OF z_Hin])
  assume z_Hip:"(~?z_hio)"
  have z_Hiq: "?z_him((CHOOSE x:(~((x \\in a_senthash_primea)=>(x \\in (((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)]))))))" (is "?z_hir=>_")
  by (rule zenon_all_0 [of "?z_him" "(CHOOSE x:(~((x \\in a_senthash_primea)=>(x \\in (((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)])))))", OF z_Hij])
  show FALSE
  proof (rule zenon_imply [OF z_Hiq])
   assume z_His:"(~?z_hir)"
   show FALSE
   proof (rule zenon_notin_setminus [of "(CHOOSE x:(~((x \\in a_senthash_primea)=>(x \\in (((([''type'' : ({''1a''}), ''bal'' : (Nat), ''from'' : (Proposers)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''voted'' : (SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''decrees'' : (SUBSET([''slot'' : (Nat), ''val'' : (Values)])), ''from'' : (Proposers)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]) \\cup [''type'' : ({''preempt''}), ''to'' : (Proposers), ''bal'' : (Nat)])))))" "?z_ho" "sent", OF z_His])
    assume z_Hit:"(~?z_hic)"
    show FALSE
    by (rule notE [OF z_Hit z_Hic])
   next
    assume z_Hio:"?z_hio"
    show FALSE
    by (rule notE [OF z_Hip z_Hio])
   qed
  next
   assume z_Hhw:"?z_hhw"
   show FALSE
   by (rule notE [OF z_Hhx z_Hhw])
  qed
 next
  assume z_Hhw:"?z_hhw"
  show FALSE
  by (rule notE [OF z_Hhx z_Hhw])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 143"; *} qed
lemma ob'249:
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Acceptors
fixes Values
fixes Quorums
fixes Proposers
fixes sent sent'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition PartialBmax suppressed *)
(* usable definition voteds suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Bmax suppressed *)
(* usable definition FreeSlots suppressed *)
(* usable definition NewProposals suppressed *)
(* usable definition ProposeDecrees suppressed *)
(* usable definition VS suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Preempt suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
assumes v'64: "(((TypeOK) \<and> (MsgInv)))"
assumes v'65: "(((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))"
fixes a
assumes a_in : "(a \<in> (Acceptors))"
fixes m
assumes m_in : "(m \<in> (sent))"
fixes a_m2a
assumes a_m2a_in : "(a_m2a \<in> ((a_senthash_primea :: c)))"
assumes v'97: "(((fapply ((a_m2a), (''type''))) = (''1b'')))"
fixes s
assumes s_in : "(s \<in> (Nat))"
fixes b
assumes b_in : "(b \<in> (Nat))"
fixes v
assumes v_in : "(v \<in> (Values))"
assumes v'107: "((a_h03062837f0f10c4714e0f53023b1a7a ((fapply ((a_m2a), (''from''))), (b), (s), (v)) :: c))"
fixes a_r3a
assumes a_r3a_in : "(a_r3a \<in> ((voteds ((fapply ((a_m2a), (''from'')))))))"
assumes v'119: "(((((fapply ((a_m2a), (''from''))) \<in> (Acceptors))) \<and> ((VotedForIn ((fapply ((a_m2a), (''from''))), (b), (s), (v))))))"
assumes v'120: "(((fapply ((a_r3a), (''bal''))) = (b)))"
assumes v'121: "(((fapply ((a_r3a), (''slot''))) = (s)))"
assumes v'122: "(((fapply ((a_r3a), (''val''))) = (v)))"
assumes v'123: "(((TypeOK) \<Rightarrow> (\<forall> a_1 \<in> (Acceptors) : (\<forall> s_1 \<in> (Nat) : (((((voteds ((a_1)))) \<in> ((SUBSET ([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)]))))) & (((\<exists> r \<in> ((voteds ((a_1)))) : (((fapply ((r), (''slot''))) = (s_1)))) \<Leftrightarrow> (\<exists> r \<in> ((PartialBmax (((voteds ((a_1))))))) : (((fapply ((r), (''slot''))) = (s_1)))))) & ((((PartialBmax (((voteds ((a_1))))))) \<subseteq> ((voteds ((a_1)))))) & (\<forall> r \<in> ((voteds ((a_1)))) : (\<exists> a_r2a \<in> ((PartialBmax (((voteds ((a_1))))))) : (((((fapply ((r), (''slot''))) = (fapply ((a_r2a), (''slot''))))) \<and> ((leq ((fapply ((r), (''bal''))), (fapply ((a_r2a), (''bal'')))))))))))))))"
shows "(\<forall> r \<in> ((voteds ((fapply ((a_m2a), (''from'')))))) : (\<exists> a_r2a \<in> ((PartialBmax (((voteds ((fapply ((a_m2a), (''from''))))))))) : (((((fapply ((r), (''slot''))) = (fapply ((a_r2a), (''slot''))))) \<and> ((leq ((fapply ((r), (''bal''))), (fapply ((a_r2a), (''bal''))))))))))"(is "PROP ?ob'249")
proof -
ML_command {* writeln "*** TLAPS ENTER 249"; *}
show "PROP ?ob'249"

(* BEGIN ZENON INPUT
;; file=MultiPaxosUs.tlaps/tlapm_ef97fd.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >MultiPaxosUs.tlaps/tlapm_ef97fd.znn.out
;; obligation #249
$hyp "v'64" (/\ TypeOK MsgInv)
$hyp "v'65" (\/ Next (= a_h4fd5f73954dc53af536c1c75068837a
vars))
$hyp "a_in" (TLA.in a Acceptors)
$hyp "m_in" (TLA.in m sent)
$hyp "a_m2a_in" (TLA.in a_m2a a_senthash_primea)
$hyp "v'97" (= (TLA.fapply a_m2a "type")
"1b")
$hyp "s_in" (TLA.in s arith.N)
$hyp "b_in" (TLA.in b arith.N)
$hyp "v_in" (TLA.in v Values)
$hyp "v'107" (a_h03062837f0f10c4714e0f53023b1a7a (TLA.fapply a_m2a "from") b
s
v)
$hyp "a_r3a_in" (TLA.in a_r3a (voteds (TLA.fapply a_m2a "from")))
$hyp "v'119" (/\ (TLA.in (TLA.fapply a_m2a "from") Acceptors)
(VotedForIn (TLA.fapply a_m2a "from") b s
v))
$hyp "v'120" (= (TLA.fapply a_r3a "bal")
b)
$hyp "v'121" (= (TLA.fapply a_r3a "slot")
s)
$hyp "v'122" (= (TLA.fapply a_r3a "val") v)
$hyp "v'123" (=> TypeOK
(TLA.bAll Acceptors ((a_1) (TLA.bAll arith.N ((s_1) (/\ (TLA.in (voteds a_1)
(TLA.SUBSET (TLA.recordset "bal" arith.N "slot" arith.N "val" Values)))
(<=> (TLA.bEx (voteds a_1) ((r) (= (TLA.fapply r "slot") s_1)))
(TLA.bEx (PartialBmax (voteds a_1)) ((r) (= (TLA.fapply r "slot") s_1))))
(TLA.subseteq (PartialBmax (voteds a_1)) (voteds a_1))
(TLA.bAll (voteds a_1) ((r) (TLA.bEx (PartialBmax (voteds a_1)) ((a_r2a) (/\ (= (TLA.fapply r "slot")
(TLA.fapply a_r2a "slot")) (arith.le (TLA.fapply r "bal")
(TLA.fapply a_r2a "bal")))))))))))))
$goal (TLA.bAll (voteds (TLA.fapply a_m2a "from")) ((r) (TLA.bEx (PartialBmax (voteds (TLA.fapply a_m2a "from"))) ((a_r2a) (/\ (= (TLA.fapply r "slot")
(TLA.fapply a_r2a "slot")) (arith.le (TLA.fapply r "bal")
(TLA.fapply a_r2a "bal")))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(TypeOK&MsgInv)"
 using v'64 by blast
 have z_Hp:"(TypeOK=>bAll(Acceptors, (\<lambda>a_1. bAll(Nat, (\<lambda>s_1. ((voteds(a_1) \\in SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)]))&((bEx(voteds(a_1), (\<lambda>r. ((r[''slot''])=s_1)))<=>bEx(PartialBmax(voteds(a_1)), (\<lambda>r. ((r[''slot''])=s_1))))&((PartialBmax(voteds(a_1)) \\subseteq voteds(a_1))&bAll(voteds(a_1), (\<lambda>r. bEx(PartialBmax(voteds(a_1)), (\<lambda>a_r2a. (((r[''slot''])=(a_r2a[''slot'']))&((r[''bal'']) <= (a_r2a[''bal''])))))))))))))))" (is "_=>?z_ht")
 using v'123 by blast
 have z_Hl:"(((a_m2a[''from'']) \\in Acceptors)&VotedForIn((a_m2a[''from'']), b, s, v))" (is "?z_hcg&?z_hck")
 using v'119 by blast
 assume z_Hq:"(~bAll(voteds((a_m2a[''from''])), (\<lambda>r. bEx(PartialBmax(voteds((a_m2a[''from'']))), (\<lambda>a_r2a. (((r[''slot''])=(a_r2a[''slot'']))&((r[''bal'']) <= (a_r2a[''bal'']))))))))" (is "~?z_hco")
 have z_Hr: "TypeOK"
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hcg: "?z_hcg"
 by (rule zenon_and_0 [OF z_Hl])
 show FALSE
 proof (rule zenon_imply [OF z_Hp])
  assume z_Hct:"(~TypeOK)"
  show FALSE
  by (rule notE [OF z_Hct z_Hr])
 next
  assume z_Ht:"?z_ht"
  have z_Hcu_z_Ht: "(\\A x:((x \\in Acceptors)=>bAll(Nat, (\<lambda>s_1. ((voteds(x) \\in SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)]))&((bEx(voteds(x), (\<lambda>r. ((r[''slot''])=s_1)))<=>bEx(PartialBmax(voteds(x)), (\<lambda>r. ((r[''slot''])=s_1))))&((PartialBmax(voteds(x)) \\subseteq voteds(x))&bAll(voteds(x), (\<lambda>r. bEx(PartialBmax(voteds(x)), (\<lambda>a_r2a. (((r[''slot''])=(a_r2a[''slot'']))&((r[''bal'']) <= (a_r2a[''bal''])))))))))))))) == ?z_ht" (is "?z_hcu == _")
  by (unfold bAll_def)
  have z_Hcu: "?z_hcu" (is "\\A x : ?z_hdn(x)")
  by (unfold z_Hcu_z_Ht, fact z_Ht)
  have z_Hdo: "?z_hdn((a_m2a[''from'']))" (is "_=>?z_hdp")
  by (rule zenon_all_0 [of "?z_hdn" "(a_m2a[''from''])", OF z_Hcu])
  show FALSE
  proof (rule zenon_imply [OF z_Hdo])
   assume z_Hdq:"(~?z_hcg)"
   show FALSE
   by (rule notE [OF z_Hdq z_Hcg])
  next
   assume z_Hdp:"?z_hdp"
   have z_Hdr_z_Hdp: "(\\A x:((x \\in Nat)=>((voteds((a_m2a[''from''])) \\in SUBSET([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)]))&((bEx(voteds((a_m2a[''from''])), (\<lambda>r. ((r[''slot''])=x)))<=>bEx(PartialBmax(voteds((a_m2a[''from'']))), (\<lambda>r. ((r[''slot''])=x))))&((PartialBmax(voteds((a_m2a[''from'']))) \\subseteq voteds((a_m2a[''from''])))&?z_hco))))) == ?z_hdp" (is "?z_hdr == _")
   by (unfold bAll_def)
   have z_Hdr: "?z_hdr" (is "\\A x : ?z_hee(x)")
   by (unfold z_Hdr_z_Hdp, fact z_Hdp)
   have z_Hef: "?z_hee(0)" (is "?z_heh=>?z_hei")
   by (rule zenon_all_0 [of "?z_hee" "0", OF z_Hdr])
   show FALSE
   proof (rule zenon_imply [OF z_Hef])
    assume z_Hej:"(~?z_heh)"
    show FALSE
    by (rule zenon_in_nat_0 [of , OF z_Hej])
   next
    assume z_Hei:"?z_hei" (is "?z_hdv&?z_hek")
    have z_Hek: "?z_hek" (is "?z_hel&?z_hec")
    by (rule zenon_and_1 [OF z_Hei])
    have z_Hec: "?z_hec" (is "?z_hed&_")
    by (rule zenon_and_1 [OF z_Hek])
    have z_Hco: "?z_hco"
    by (rule zenon_and_1 [OF z_Hec])
    show FALSE
    by (rule notE [OF z_Hq z_Hco])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 249"; *} qed
lemma ob'269:
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Acceptors
fixes Values
fixes Quorums
fixes Proposers
fixes sent sent'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition PartialBmax suppressed *)
(* usable definition voteds suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Bmax suppressed *)
(* usable definition FreeSlots suppressed *)
(* usable definition NewProposals suppressed *)
(* usable definition ProposeDecrees suppressed *)
(* usable definition VS suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Preempt suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
assumes v'63: "(((TypeOK) \<and> (MsgInv)))"
assumes v'64: "(((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))"
fixes p
assumes p_in : "(p \<in> (Proposers))"
fixes m
assumes m_in : "(m \<in> ((a_senthash_primea :: c)))"
assumes v'84: "(\<exists> b \<in> (Nat) : (((~ (\<exists> m_1 \<in> (sent) : (((((fapply ((m_1), (''type''))) = (''2a''))) \<and> (((fapply ((m_1), (''bal''))) = (b)))))))) & (\<exists> Q \<in> (Quorums) : (\<exists> S \<in> ((SUBSET (subsetOf((sent), %m_1. (((((fapply ((m_1), (''type''))) = (''1b''))) \<and> (((fapply ((m_1), (''bal''))) = (b))))))))) : ((\<forall> a \<in> (Q) : (\<exists> m_1 \<in> (S) : (((fapply ((m_1), (''from''))) = (a))))) & ((Send (({(((''type'' :> (''2a'')) @@ (''from'' :> (p)) @@ (''bal'' :> (b)) @@ (''decrees'' :> ((ProposeDecrees (((VS ((S), (Q))))))))))})))))))))"
shows "(\<exists> b \<in> (Nat) : (\<exists> Q \<in> (Quorums) : (\<exists> S \<in> ((SUBSET (sent))) : (((~ (\<exists> a_m2a \<in> (sent) : (((((fapply ((a_m2a), (''type''))) = (''2a''))) \<and> (((fapply ((a_m2a), (''bal''))) = (b)))))))) & (((S) \<in> ((SUBSET (subsetOf((sent), %a_m2a. (((((fapply ((a_m2a), (''type''))) = (''1b''))) \<and> (((fapply ((a_m2a), (''bal''))) = (b))))))))))) & (\<forall> a \<in> (Q) : (\<exists> a_m2a \<in> (S) : (((fapply ((a_m2a), (''from''))) = (a))))) & ((Send (({(((''type'' :> (''2a'')) @@ (''bal'' :> (b)) @@ (''from'' :> (p)) @@ (''decrees'' :> ((ProposeDecrees (((VS ((S), (Q))))))))))}))))))))"(is "PROP ?ob'269")
proof -
ML_command {* writeln "*** TLAPS ENTER 269"; *}
show "PROP ?ob'269"

(* BEGIN ZENON INPUT
;; file=MultiPaxosUs.tlaps/tlapm_33077f.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >MultiPaxosUs.tlaps/tlapm_33077f.znn.out
;; obligation #269
$hyp "v'63" (/\ TypeOK MsgInv)
$hyp "v'64" (\/ Next (= a_h4fd5f73954dc53af536c1c75068837a
vars))
$hyp "p_in" (TLA.in p Proposers)
$hyp "m_in" (TLA.in m a_senthash_primea)
$hyp "v'84" (TLA.bEx arith.N ((b) (/\ (-. (TLA.bEx sent ((m_1) (/\ (= (TLA.fapply m_1 "type")
"2a") (= (TLA.fapply m_1 "bal") b)))))
(TLA.bEx Quorums ((Q) (TLA.bEx (TLA.SUBSET (TLA.subsetOf sent ((m_1) (/\ (= (TLA.fapply m_1 "type")
"1b") (= (TLA.fapply m_1 "bal")
b))))) ((S) (/\ (TLA.bAll Q ((a) (TLA.bEx S ((m_1) (= (TLA.fapply m_1 "from")
a)))))
(Send (TLA.set (TLA.record "type" "2a" "from" p "bal" b "decrees" (ProposeDecrees (VS S
Q)))))))))))))
$goal (TLA.bEx arith.N ((b) (TLA.bEx Quorums ((Q) (TLA.bEx (TLA.SUBSET sent) ((S) (/\ (-. (TLA.bEx sent ((a_m2a) (/\ (= (TLA.fapply a_m2a "type")
"2a") (= (TLA.fapply a_m2a "bal") b))))) (TLA.in S
(TLA.SUBSET (TLA.subsetOf sent ((a_m2a) (/\ (= (TLA.fapply a_m2a "type")
"1b") (= (TLA.fapply a_m2a "bal") b))))))
(TLA.bAll Q ((a) (TLA.bEx S ((a_m2a) (= (TLA.fapply a_m2a "from") a)))))
(Send (TLA.set (TLA.record "type" "2a" "bal" b "from" p "decrees" (ProposeDecrees (VS S
Q))))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_He:"bEx(Nat, (\<lambda>b. ((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=b)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=b))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (b) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))" (is "?z_he")
 using v'84 by blast
 assume z_Hf:"(~bEx(Nat, (\<lambda>b. bEx(Quorums, (\<lambda>Q. bEx(SUBSET(sent), (\<lambda>S. ((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=b)))))&((S \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=b))))))&(bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''from'' :> (p) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))" (is "~?z_hca")
 have z_Hco_z_He: "(\\E x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))}))))))))) == ?z_he" (is "?z_hco == _")
 by (unfold bEx_def)
 have z_Hco: "?z_hco" (is "\\E x : ?z_hdk(x)")
 by (unfold z_Hco_z_He, fact z_He)
 have z_Hdl: "?z_hdk((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))}))))))))))" (is "?z_hdn&?z_hdo")
 by (rule zenon_ex_choose_0 [of "?z_hdk", OF z_Hco])
 have z_Hdn: "?z_hdn"
 by (rule zenon_and_0 [OF z_Hdl])
 have z_Hdo: "?z_hdo" (is "?z_hdp&?z_hdq")
 by (rule zenon_and_1 [OF z_Hdl])
 have z_Hdp: "?z_hdp" (is "~?z_hdr")
 by (rule zenon_and_0 [OF z_Hdo])
 have z_Hdq: "?z_hdq"
 by (rule zenon_and_1 [OF z_Hdo])
 have z_Hds_z_Hdq: "(\\E x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))) == ?z_hdq" (is "?z_hds == _")
 by (unfold bEx_def)
 have z_Hds: "?z_hds" (is "\\E x : ?z_hej(x)")
 by (unfold z_Hds_z_Hdq, fact z_Hdq)
 have z_Hek: "?z_hej((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))))" (is "?z_hem&?z_hen")
 by (rule zenon_ex_choose_0 [of "?z_hej", OF z_Hds])
 have z_Hem: "?z_hem"
 by (rule zenon_and_0 [OF z_Hek])
 have z_Hen: "?z_hen"
 by (rule zenon_and_1 [OF z_Hek])
 have z_Heo_z_Hen: "(\\E x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))) == ?z_hen" (is "?z_heo == _")
 by (unfold bEx_def)
 have z_Heo: "?z_heo" (is "\\E x : ?z_hfa(x)")
 by (unfold z_Heo_z_Hen, fact z_Hen)
 have z_Hfb: "?z_hfa((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))" (is "?z_hfd&?z_hfe")
 by (rule zenon_ex_choose_0 [of "?z_hfa", OF z_Heo])
 have z_Hfd: "?z_hfd"
 by (rule zenon_and_0 [OF z_Hfb])
 have z_Hfe: "?z_hfe" (is "?z_hff&?z_hfg")
 by (rule zenon_and_1 [OF z_Hfb])
 have z_Hff: "?z_hff"
 by (rule zenon_and_0 [OF z_Hfe])
 have z_Hfg: "?z_hfg"
 by (rule zenon_and_1 [OF z_Hfe])
 have z_Hfh: "((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))) \\subseteq subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))}))))))))))))))" (is "?z_hfh")
 by (rule zenon_in_SUBSET_0 [of "(CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))}))))" "subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))", OF z_Hfd])
 have z_Hfi_z_Hfh: "bAll((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))), (\<lambda>x. (x \\in subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))) == ?z_hfh" (is "?z_hfi == _")
 by (unfold subset_def)
 have z_Hfi: "?z_hfi"
 by (unfold z_Hfi_z_Hfh, fact z_Hfh)
 have z_Hfl_z_Hfi: "(\\A x:((x \\in (CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))=>(x \\in subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))) == ?z_hfi" (is "?z_hfl == _")
 by (unfold bAll_def)
 have z_Hfl: "?z_hfl" (is "\\A x : ?z_hfo(x)")
 by (unfold z_Hfl_z_Hfi, fact z_Hfi)
 have z_Hfp_z_Hf: "(~(\\E x:((x \\in Nat)&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(sent), (\<lambda>S. ((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&((S \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))))&(bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''bal'' :> (x) @@ ''from'' :> (p) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))}))))))))))) == (~?z_hca)" (is "?z_hfp == ?z_hf")
 by (unfold bEx_def)
 have z_Hfp: "?z_hfp" (is "~(\\E x : ?z_hgd(x))")
 by (unfold z_Hfp_z_Hf, fact z_Hf)
 have z_Hge: "~?z_hgd((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))}))))))))))" (is "~(_&?z_hgf)")
 by (rule zenon_notex_0 [of "?z_hgd" "(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))", OF z_Hfp])
 show FALSE
 proof (rule zenon_notand [OF z_Hge])
  assume z_Hgg:"(~?z_hdn)"
  show FALSE
  by (rule notE [OF z_Hgg z_Hdn])
 next
  assume z_Hgh:"(~?z_hgf)"
  have z_Hgi_z_Hgh: "(~(\\E x:((x \\in Quorums)&bEx(SUBSET(sent), (\<lambda>S. (?z_hdp&((S \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''from'' :> (p) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))) == (~?z_hgf)" (is "?z_hgi == ?z_hgh")
  by (unfold bEx_def)
  have z_Hgi: "?z_hgi" (is "~(\\E x : ?z_hgu(x))")
  by (unfold z_Hgi_z_Hgh, fact z_Hgh)
  have z_Hgv: "~?z_hgu((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))))" (is "~(_&?z_hgw)")
  by (rule zenon_notex_0 [of "?z_hgu" "(CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))", OF z_Hgi])
  show FALSE
  proof (rule zenon_notand [OF z_Hgv])
   assume z_Hgx:"(~?z_hem)"
   show FALSE
   by (rule notE [OF z_Hgx z_Hem])
  next
   assume z_Hgy:"(~?z_hgw)"
   have z_Hgz_z_Hgy: "(~(\\E x:((x \\in SUBSET(sent))&(?z_hdp&((x \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''from'' :> (p) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))}))))))) == (~?z_hgw)" (is "?z_hgz == ?z_hgy")
   by (unfold bEx_def)
   have z_Hgz: "?z_hgz" (is "~(\\E x : ?z_hhj(x))")
   by (unfold z_Hgz_z_Hgy, fact z_Hgy)
   have z_Hhk: "~?z_hhj((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))" (is "~(?z_hhl&?z_hhm)")
   by (rule zenon_notex_0 [of "?z_hhj" "(CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))}))))", OF z_Hgz])
   show FALSE
   proof (rule zenon_notand [OF z_Hhk])
    assume z_Hhn:"(~?z_hhl)"
    have z_Hho: "(~((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))) \\subseteq sent))" (is "~?z_hhp")
    by (rule zenon_notin_SUBSET_0 [of "(CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))}))))" "sent", OF z_Hhn])
    have z_Hhq_z_Hho: "(~bAll((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))), (\<lambda>zenon_Vkb. (zenon_Vkb \\in sent)))) == (~?z_hhp)" (is "?z_hhq == ?z_hho")
    by (unfold subset_def)
    have z_Hhq: "?z_hhq" (is "~?z_hhr")
    by (unfold z_Hhq_z_Hho, fact z_Hho)
    have z_Hhv_z_Hhq: "(~(\\A x:((x \\in (CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))=>(x \\in sent)))) == ?z_hhq" (is "?z_hhv == _")
    by (unfold bAll_def)
    have z_Hhv: "?z_hhv" (is "~(\\A x : ?z_hhz(x))")
    by (unfold z_Hhv_z_Hhq, fact z_Hhq)
    have z_Hia: "(\\E x:(~((x \\in (CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))=>(x \\in sent))))" (is "\\E x : ?z_hic(x)")
    by (rule zenon_notallex_0 [of "?z_hhz", OF z_Hhv])
    have z_Hid: "?z_hic((CHOOSE x:(~((x \\in (CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))=>(x \\in sent)))))" (is "~(?z_hif=>?z_hig)")
    by (rule zenon_ex_choose_0 [of "?z_hic", OF z_Hia])
    have z_Hif: "?z_hif"
    by (rule zenon_notimply_0 [OF z_Hid])
    have z_Hih: "(~?z_hig)"
    by (rule zenon_notimply_1 [OF z_Hid])
    have z_Hii: "?z_hfo((CHOOSE x:(~((x \\in (CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))=>(x \\in sent)))))" (is "_=>?z_hij")
    by (rule zenon_all_0 [of "?z_hfo" "(CHOOSE x:(~((x \\in (CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))=>(x \\in sent))))", OF z_Hfl])
    show FALSE
    proof (rule zenon_imply [OF z_Hii])
     assume z_Hik:"(~?z_hif)"
     show FALSE
     by (rule notE [OF z_Hik z_Hif])
    next
     assume z_Hij:"?z_hij"
     have z_Hig: "?z_hig"
     by (rule zenon_in_subsetof_0 [of "(CHOOSE x:(~((x \\in (CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))))=>(x \\in sent))))" "sent" "(\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))}))))))))))))", OF z_Hij])
     show FALSE
     by (rule notE [OF z_Hih z_Hig])
    qed
   next
    assume z_Hil:"(~?z_hhm)" (is "~(_&?z_him)")
    show FALSE
    proof (rule zenon_notand [OF z_Hil])
     assume z_Hin:"(~?z_hdp)"
     show FALSE
     by (rule notE [OF z_Hin z_Hdp])
    next
     assume z_Hio:"(~?z_him)" (is "~(_&?z_hip)")
     show FALSE
     proof (rule zenon_notand [OF z_Hio])
      assume z_Hiq:"(~?z_hfd)"
      show FALSE
      by (rule notE [OF z_Hiq z_Hfd])
     next
      assume z_Hir:"(~?z_hip)" (is "~(_&?z_his)")
      show FALSE
      proof (rule zenon_notand [OF z_Hir])
       assume z_Hit:"(~?z_hff)"
       show FALSE
       by (rule notE [OF z_Hit z_Hff])
      next
       assume z_Hiu:"(~?z_his)"
       show FALSE
       proof (rule notE [OF z_Hiu])
        have z_Hiv: "({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))), (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))}={(''type'' :> (''2a'') @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''from'' :> (p) @@ ''decrees'' :> (ProposeDecrees(VS((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))), (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})" (is "?z_hiw=?z_hja")
        proof (rule zenon_nnpp [of "(?z_hiw=?z_hja)"])
         assume z_Hjc:"(?z_hiw~=?z_hja)"
         show FALSE
         proof (rule zenon_noteq [of "?z_hja"])
          have z_Hjd: "((''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))), (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))=(''type'' :> (''2a'') @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''from'' :> (p) @@ ''decrees'' :> (ProposeDecrees(VS((CHOOSE x:((x \\in SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))))&(bAll((CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))), (\<lambda>a. bEx(x, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(x, (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))}))))))))))})))), (CHOOSE x:((x \\in Quorums)&bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=(CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))))))), (\<lambda>S. (bAll(x, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> ((CHOOSE x:((x \\in Nat)&((~bEx(sent, (\<lambda>m_1. (((m_1[''type''])=''2a'')&((m_1[''bal''])=x)))))&bEx(Quorums, (\<lambda>Q. bEx(SUBSET(subsetOf(sent, (\<lambda>m_1. (((m_1[''type''])=''1b'')&((m_1[''bal''])=x))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m_1. ((m_1[''from''])=a)))))&Send({(''type'' :> (''2a'') @@ ''from'' :> (p) @@ ''bal'' :> (x) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})))))))))) @@ ''decrees'' :> (ProposeDecrees(VS(S, x))))})))))))))))" (is "?z_hix=?z_hjb")
          proof (rule zenon_nnpp [of "(?z_hix=?z_hjb)"])
           assume z_Hje:"(?z_hix~=?z_hjb)"
           sorry
          qed
          have z_Hjf: "(?z_hja~=?z_hja)"
          by (rule subst [where P="(\<lambda>zenon_Vjf. ({zenon_Vjf}~=?z_hja))", OF z_Hjd], fact z_Hjc)
          thus "(?z_hja~=?z_hja)" .
         qed
        qed
        have z_His: "?z_his"
        by (rule subst [where P="(\<lambda>zenon_Vkf. Send(zenon_Vkf))", OF z_Hiv], fact z_Hfg)
        thus "?z_his" .
       qed
      qed
     qed
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 269"; *} qed
lemma ob'23:
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Acceptors
fixes Values
fixes Quorums
fixes Proposers
(* usable definition Ballots suppressed *)
(* usable definition Slots suppressed *)
fixes sent sent'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition sent1b2b suppressed *)
(* usable definition PartialBmax suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Bmax suppressed *)
(* usable definition FreeSlots suppressed *)
(* usable definition NewProposals suppressed *)
(* usable definition ProposeDecrees suppressed *)
(* usable definition VS suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Preempt suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
shows "(\<forall>a : (\<forall>b : (\<forall>s : (\<forall>v : (((\<exists> m \<in> (sent) : ((((fapply ((m), (''type''))) = (''2b''))) & (((fapply ((m), (''bal''))) = (b))) & (((fapply ((m), (''slot''))) = (s))) & (((fapply ((m), (''val''))) = (v))) & (((fapply ((m), (''from''))) = (a))))) \<Leftrightarrow> (\<exists> r \<in> (setOfAll((subsetOf((sent), %m. (((((fapply ((m), (''type''))) = (''2b''))) \<and> (((fapply ((m), (''from''))) = (a))))))), %m. (((''bal'' :> (fapply ((m), (''bal'')))) @@ (''slot'' :> (fapply ((m), (''slot'')))) @@ (''val'' :> (fapply ((m), (''val'')))))))) : (((((((fapply ((r), (''bal''))) = (b))) \<and> (((fapply ((r), (''slot''))) = (s))))) \<and> (((fapply ((r), (''val''))) = (v))))))))))))"(is "PROP ?ob'23")
proof -
ML_command {* writeln "*** TLAPS ENTER 23"; *}
show "PROP ?ob'23"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 23"; *} qed
lemma ob'296:
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Acceptors
fixes Values
fixes Quorums
fixes Proposers
fixes sent sent'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition PartialBmax suppressed *)
(* usable definition voteds suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Bmax suppressed *)
(* usable definition FreeSlots suppressed *)
(* usable definition ProposeDecrees suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Preempt suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
assumes v'62: "(((TypeOK) \<and> (MsgInv)))"
assumes v'63: "(((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))"
fixes p
assumes p_in : "(p \<in> (Proposers))"
fixes m
assumes m_in : "(m \<in> ((a_senthash_primea :: c)))"
fixes b
assumes b_in : "(b \<in> (Nat))"
fixes Q
assumes Q_in : "(Q \<in> (Quorums))"
fixes S
assumes S_in : "(S \<in> ((SUBSET (sent))))"
assumes v'85: "(((~ (\<exists> a_m2a \<in> (sent) : (((((fapply ((a_m2a), (''type''))) = (''2a''))) \<and> (((fapply ((a_m2a), (''bal''))) = (b)))))))) & (((S) \<in> ((SUBSET (subsetOf((sent), %a_m2a. (((((fapply ((a_m2a), (''type''))) = (''1b''))) \<and> (((fapply ((a_m2a), (''bal''))) = (b))))))))))) & (\<forall> a \<in> (Q) : (\<exists> a_m2a \<in> (S) : (((fapply ((a_m2a), (''from''))) = (a))))) & ((Send (({(((''type'' :> (''2a'')) @@ (''bal'' :> (b)) @@ (''from'' :> (p)) @@ (''decrees'' :> ((ProposeDecrees (((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted'')))))))))))))})))))"
assumes v'92: "(((fapply ((m), (''type''))) = (''2a'')))"
assumes v'101: "(\<forall> d \<in> ((([''slot'' : ((FreeSlots (((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted'')))))))))), ''val'' : (Values)]) \\ ({}))) : ((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((b), (fapply ((d), (''slot''))), (fapply ((d), (''val'')))) :: c)))"
assumes v'102: "(\<forall>S_1 : ((((bChoice(((SUBSET ((([''slot'' : ((FreeSlots ((S_1)))), ''val'' : (Values)]) \\ ({}))))), %D. (\<forall> a_d1a \<in> (D) : (\<forall> a_d2a \<in> (D) : (((((fapply ((a_d1a), (''slot''))) = (fapply ((a_d2a), (''slot''))))) \<Rightarrow> (((a_d1a) = (a_d2a))))))))) \<in> ((((SUBSET ([''slot'' : ((FreeSlots ((S_1)))), ''val'' : (Values)]))) \\ ({}))))) & (\<forall> a_t1a \<in> (bChoice(((SUBSET ((([''slot'' : ((FreeSlots ((S_1)))), ''val'' : (Values)]) \\ ({}))))), %D. (\<forall> a_d1a \<in> (D) : (\<forall> a_d2a \<in> (D) : (((((fapply ((a_d1a), (''slot''))) = (fapply ((a_d2a), (''slot''))))) \<Rightarrow> (((a_d1a) = (a_d2a))))))))) : (\<forall> a_t2a \<in> (bChoice(((SUBSET ((([''slot'' : ((FreeSlots ((S_1)))), ''val'' : (Values)]) \\ ({}))))), %D. (\<forall> a_d1a \<in> (D) : (\<forall> a_d2a \<in> (D) : (((((fapply ((a_d1a), (''slot''))) = (fapply ((a_d2a), (''slot''))))) \<Rightarrow> (((a_d1a) = (a_d2a))))))))) : (((((fapply ((a_t1a), (''slot''))) = (fapply ((a_t2a), (''slot''))))) \<Rightarrow> (((a_t1a) = (a_t2a))))))) & ((~ (\<exists> a_t1a \<in> ((Bmax ((S_1)))) : (\<exists> a_t2a \<in> (bChoice(((SUBSET ((([''slot'' : ((FreeSlots ((S_1)))), ''val'' : (Values)]) \\ ({}))))), %D. (\<forall> a_d1a \<in> (D) : (\<forall> a_d2a \<in> (D) : (((((fapply ((a_d1a), (''slot''))) = (fapply ((a_d2a), (''slot''))))) \<Rightarrow> (((a_d1a) = (a_d2a))))))))) : (((fapply ((a_t1a), (''slot''))) = (fapply ((a_t2a), (''slot'')))))))))))"
shows "(\<forall> d \<in> (bChoice(((SUBSET ((([''slot'' : ((FreeSlots (((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted'')))))))))), ''val'' : (Values)]) \\ ({}))))), %D. (\<forall> a_d1a \<in> (D) : (\<forall> a_d2a \<in> (D) : (((((fapply ((a_d1a), (''slot''))) = (fapply ((a_d2a), (''slot''))))) \<Rightarrow> (((a_d1a) = (a_d2a))))))))) : ((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((b), (fapply ((d), (''slot''))), (fapply ((d), (''val'')))) :: c)))"(is "PROP ?ob'296")
proof -
ML_command {* writeln "*** TLAPS ENTER 296"; *}
show "PROP ?ob'296"

(* BEGIN ZENON INPUT
;; file=MultiPaxosUs.tlaps/tlapm_2a16c2.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >MultiPaxosUs.tlaps/tlapm_2a16c2.znn.out
;; obligation #296
$hyp "v'62" (/\ TypeOK MsgInv)
$hyp "v'63" (\/ Next (= a_h4fd5f73954dc53af536c1c75068837a
vars))
$hyp "p_in" (TLA.in p Proposers)
$hyp "m_in" (TLA.in m a_senthash_primea)
$hyp "b_in" (TLA.in b arith.N)
$hyp "Q_in" (TLA.in Q Quorums)
$hyp "S_in" (TLA.in S (TLA.SUBSET sent))
$hyp "v'85" (/\ (-. (TLA.bEx sent ((a_m2a) (/\ (= (TLA.fapply a_m2a "type")
"2a") (= (TLA.fapply a_m2a "bal") b))))) (TLA.in S
(TLA.SUBSET (TLA.subsetOf sent ((a_m2a) (/\ (= (TLA.fapply a_m2a "type")
"1b") (= (TLA.fapply a_m2a "bal") b))))))
(TLA.bAll Q ((a) (TLA.bEx S ((a_m2a) (= (TLA.fapply a_m2a "from") a)))))
(Send (TLA.set (TLA.record "type" "2a" "bal" b "from" p "decrees" (ProposeDecrees (TLA.UNION (TLA.setOfAll (TLA.subsetOf S ((m_1) (TLA.in (TLA.fapply m_1 "from")
Q))) ((m_1) (TLA.fapply m_1 "voted")))))))))
$hyp "v'92" (= (TLA.fapply m "type")
"2a")
$hyp "v'101" (TLA.bAll (TLA.setminus (TLA.recordset "slot" (FreeSlots (TLA.UNION (TLA.setOfAll (TLA.subsetOf S ((m_1) (TLA.in (TLA.fapply m_1 "from")
Q))) ((m_1) (TLA.fapply m_1 "voted"))))) "val" Values)
TLA.emptyset) ((d) (a_hd4a7fa801d94bc2a9c69d39a405ea2a b
(TLA.fapply d "slot")
(TLA.fapply d "val"))))
$hyp "v'102" (A. ((S_1) (/\ (TLA.in (TLA.bChoice (TLA.SUBSET (TLA.setminus (TLA.recordset "slot" (FreeSlots S_1) "val" Values)
TLA.emptyset)) ((D) (TLA.bAll D ((a_d1a) (TLA.bAll D ((a_d2a) (=> (= (TLA.fapply a_d1a "slot")
(TLA.fapply a_d2a "slot")) (= a_d1a a_d2a))))))))
(TLA.setminus (TLA.SUBSET (TLA.recordset "slot" (FreeSlots S_1) "val" Values))
TLA.emptyset))
(TLA.bAll (TLA.bChoice (TLA.SUBSET (TLA.setminus (TLA.recordset "slot" (FreeSlots S_1) "val" Values)
TLA.emptyset)) ((D) (TLA.bAll D ((a_d1a) (TLA.bAll D ((a_d2a) (=> (= (TLA.fapply a_d1a "slot")
(TLA.fapply a_d2a "slot")) (= a_d1a
a_d2a)))))))) ((a_t1a) (TLA.bAll (TLA.bChoice (TLA.SUBSET (TLA.setminus (TLA.recordset "slot" (FreeSlots S_1) "val" Values)
TLA.emptyset)) ((D) (TLA.bAll D ((a_d1a) (TLA.bAll D ((a_d2a) (=> (= (TLA.fapply a_d1a "slot")
(TLA.fapply a_d2a "slot")) (= a_d1a
a_d2a)))))))) ((a_t2a) (=> (= (TLA.fapply a_t1a "slot")
(TLA.fapply a_t2a "slot")) (= a_t1a a_t2a))))))
(-. (TLA.bEx (Bmax S_1) ((a_t1a) (TLA.bEx (TLA.bChoice (TLA.SUBSET (TLA.setminus (TLA.recordset "slot" (FreeSlots S_1) "val" Values)
TLA.emptyset)) ((D) (TLA.bAll D ((a_d1a) (TLA.bAll D ((a_d2a) (=> (= (TLA.fapply a_d1a "slot")
(TLA.fapply a_d2a "slot")) (= a_d1a
a_d2a)))))))) ((a_t2a) (= (TLA.fapply a_t1a "slot")
(TLA.fapply a_t2a "slot"))))))))))
$goal (TLA.bAll (TLA.bChoice (TLA.SUBSET (TLA.setminus (TLA.recordset "slot" (FreeSlots (TLA.UNION (TLA.setOfAll (TLA.subsetOf S ((m_1) (TLA.in (TLA.fapply m_1 "from")
Q))) ((m_1) (TLA.fapply m_1 "voted"))))) "val" Values)
TLA.emptyset)) ((D) (TLA.bAll D ((a_d1a) (TLA.bAll D ((a_d2a) (=> (= (TLA.fapply a_d1a "slot")
(TLA.fapply a_d2a "slot")) (= a_d1a
a_d2a)))))))) ((d) (a_hd4a7fa801d94bc2a9c69d39a405ea2a b
(TLA.fapply d "slot")
(TLA.fapply d "val"))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hj:"bAll(([''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)] \\ {}), (\<lambda>d. a_hd4a7fa801d94bc2a9c69d39a405ea2a(b, (d[''slot'']), (d[''val'']))))" (is "?z_hj")
 using v'101 by blast
 have z_Hk:"(\\A S_1:((bChoice(SUBSET(([''slot'' : (FreeSlots(S_1)), ''val'' : (Values)] \\ {})), (\<lambda>D. bAll(D, (\<lambda>a_d1a. bAll(D, (\<lambda>a_d2a. (((a_d1a[''slot''])=(a_d2a[''slot'']))=>(a_d1a=a_d2a)))))))) \\in (SUBSET([''slot'' : (FreeSlots(S_1)), ''val'' : (Values)]) \\ {}))&(bAll(bChoice(SUBSET(([''slot'' : (FreeSlots(S_1)), ''val'' : (Values)] \\ {})), (\<lambda>D. bAll(D, (\<lambda>a_d1a. bAll(D, (\<lambda>a_d2a. (((a_d1a[''slot''])=(a_d2a[''slot'']))=>(a_d1a=a_d2a)))))))), (\<lambda>a_t1a. bAll(bChoice(SUBSET(([''slot'' : (FreeSlots(S_1)), ''val'' : (Values)] \\ {})), (\<lambda>D. bAll(D, (\<lambda>a_d1a. bAll(D, (\<lambda>a_d2a. (((a_d1a[''slot''])=(a_d2a[''slot'']))=>(a_d1a=a_d2a)))))))), (\<lambda>a_t2a. (((a_t1a[''slot''])=(a_t2a[''slot'']))=>(a_t1a=a_t2a))))))&(~bEx(Bmax(S_1), (\<lambda>a_t1a. bEx(bChoice(SUBSET(([''slot'' : (FreeSlots(S_1)), ''val'' : (Values)] \\ {})), (\<lambda>D. bAll(D, (\<lambda>a_d1a. bAll(D, (\<lambda>a_d2a. (((a_d1a[''slot''])=(a_d2a[''slot'']))=>(a_d1a=a_d2a)))))))), (\<lambda>a_t2a. ((a_t1a[''slot''])=(a_t2a[''slot'']))))))))))" (is "\\A x : ?z_hdb(x)")
 using v'102 by blast
 assume z_Hl:"(~bAll(bChoice(SUBSET(([''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)] \\ {})), (\<lambda>D. bAll(D, (\<lambda>a_d1a. bAll(D, (\<lambda>a_d2a. (((a_d1a[''slot''])=(a_d2a[''slot'']))=>(a_d1a=a_d2a)))))))), (\<lambda>d. a_hd4a7fa801d94bc2a9c69d39a405ea2a(b, (d[''slot'']), (d[''val''])))))" (is "~?z_hdc")
 have z_Hdf_z_Hj: "(\\A x:((x \\in ([''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)] \\ {}))=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(b, (x[''slot'']), (x[''val''])))) == ?z_hj" (is "?z_hdf == _")
 by (unfold bAll_def)
 have z_Hdf: "?z_hdf" (is "\\A x : ?z_hdm(x)")
 by (unfold z_Hdf_z_Hj, fact z_Hj)
 have z_Hdn_z_Hl: "(~bAll((CHOOSE x:((x \\in SUBSET(([''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)] \\ {})))&bAll(x, (\<lambda>a_d1a. bAll(x, (\<lambda>a_d2a. (((a_d1a[''slot''])=(a_d2a[''slot'']))=>(a_d1a=a_d2a)))))))), (\<lambda>d. a_hd4a7fa801d94bc2a9c69d39a405ea2a(b, (d[''slot'']), (d[''val'']))))) == (~?z_hdc)" (is "?z_hdn == ?z_hl")
 by (unfold bChoose_def)
 have z_Hdn: "?z_hdn" (is "~?z_hdo")
 by (unfold z_Hdn_z_Hl, fact z_Hl)
 have z_Hdv_z_Hdn: "(~(\\A x:((x \\in (CHOOSE x:((x \\in SUBSET(([''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)] \\ {})))&bAll(x, (\<lambda>a_d1a. bAll(x, (\<lambda>a_d2a. (((a_d1a[''slot''])=(a_d2a[''slot'']))=>(a_d1a=a_d2a)))))))))=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(b, (x[''slot'']), (x[''val'']))))) == ?z_hdn" (is "?z_hdv == _")
 by (unfold bAll_def)
 have z_Hdv: "?z_hdv" (is "~(\\A x : ?z_hdz(x))")
 by (unfold z_Hdv_z_Hdn, fact z_Hdn)
 have z_Hea: "(\\E x:(~((x \\in (CHOOSE x:((x \\in SUBSET(([''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)] \\ {})))&bAll(x, (\<lambda>a_d1a. bAll(x, (\<lambda>a_d2a. (((a_d1a[''slot''])=(a_d2a[''slot'']))=>(a_d1a=a_d2a)))))))))=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(b, (x[''slot'']), (x[''val''])))))" (is "\\E x : ?z_hec(x)")
 by (rule zenon_notallex_0 [of "?z_hdz", OF z_Hdv])
 have z_Hed: "?z_hec((CHOOSE x:(~((x \\in (CHOOSE x:((x \\in SUBSET(([''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)] \\ {})))&bAll(x, (\<lambda>a_d1a. bAll(x, (\<lambda>a_d2a. (((a_d1a[''slot''])=(a_d2a[''slot'']))=>(a_d1a=a_d2a)))))))))=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(b, (x[''slot'']), (x[''val'']))))))" (is "~(?z_hef=>?z_heg)")
 by (rule zenon_ex_choose_0 [of "?z_hec", OF z_Hea])
 have z_Hef: "?z_hef"
 by (rule zenon_notimply_0 [OF z_Hed])
 have z_Heh: "(~?z_heg)"
 by (rule zenon_notimply_1 [OF z_Hed])
 have z_Hei: "?z_hdm((CHOOSE x:(~((x \\in (CHOOSE x:((x \\in SUBSET(([''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)] \\ {})))&bAll(x, (\<lambda>a_d1a. bAll(x, (\<lambda>a_d2a. (((a_d1a[''slot''])=(a_d2a[''slot'']))=>(a_d1a=a_d2a)))))))))=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(b, (x[''slot'']), (x[''val'']))))))" (is "?z_hej=>_")
 by (rule zenon_all_0 [of "?z_hdm" "(CHOOSE x:(~((x \\in (CHOOSE x:((x \\in SUBSET(([''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)] \\ {})))&bAll(x, (\<lambda>a_d1a. bAll(x, (\<lambda>a_d2a. (((a_d1a[''slot''])=(a_d2a[''slot'']))=>(a_d1a=a_d2a)))))))))=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(b, (x[''slot'']), (x[''val''])))))", OF z_Hdf])
 show FALSE
 proof (rule zenon_imply [OF z_Hei])
  assume z_Hek:"(~?z_hej)"
  show FALSE
  proof (rule zenon_notin_setminus [of "(CHOOSE x:(~((x \\in (CHOOSE x:((x \\in SUBSET(([''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)] \\ {})))&bAll(x, (\<lambda>a_d1a. bAll(x, (\<lambda>a_d2a. (((a_d1a[''slot''])=(a_d2a[''slot'']))=>(a_d1a=a_d2a)))))))))=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(b, (x[''slot'']), (x[''val''])))))" "[''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)]" "{}", OF z_Hek])
   assume z_Hel:"(~((CHOOSE x:(~((x \\in (CHOOSE x:((x \\in SUBSET(([''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)] \\ {})))&bAll(x, (\<lambda>a_d1a. bAll(x, (\<lambda>a_d2a. (((a_d1a[''slot''])=(a_d2a[''slot'']))=>(a_d1a=a_d2a)))))))))=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(b, (x[''slot'']), (x[''val'']))))) \\in [''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)]))" (is "~?z_hem")
   have z_Hen: "?z_hdb(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))" (is "?z_heo&?z_hep")
   by (rule zenon_all_0 [of "?z_hdb" "UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))", OF z_Hk])
   have z_Heo: "?z_heo"
   by (rule zenon_and_0 [OF z_Hen])
   have z_Heq: "(bChoice(SUBSET(([''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)] \\ {})), (\<lambda>D. bAll(D, (\<lambda>a_d1a. bAll(D, (\<lambda>a_d2a. (((a_d1a[''slot''])=(a_d2a[''slot'']))=>(a_d1a=a_d2a)))))))) \\in SUBSET([''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)]))" (is "?z_heq")
   by (rule zenon_in_setminus_0 [of "bChoice(SUBSET(([''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)] \\ {})), (\<lambda>D. bAll(D, (\<lambda>a_d1a. bAll(D, (\<lambda>a_d2a. (((a_d1a[''slot''])=(a_d2a[''slot'']))=>(a_d1a=a_d2a))))))))" "SUBSET([''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)])" "{}", OF z_Heo])
   have z_Hes: "(bChoice(SUBSET(([''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)] \\ {})), (\<lambda>D. bAll(D, (\<lambda>a_d1a. bAll(D, (\<lambda>a_d2a. (((a_d1a[''slot''])=(a_d2a[''slot'']))=>(a_d1a=a_d2a)))))))) \\subseteq [''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)])" (is "?z_hes")
   by (rule zenon_in_SUBSET_0 [of "bChoice(SUBSET(([''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)] \\ {})), (\<lambda>D. bAll(D, (\<lambda>a_d1a. bAll(D, (\<lambda>a_d2a. (((a_d1a[''slot''])=(a_d2a[''slot'']))=>(a_d1a=a_d2a))))))))" "[''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)]", OF z_Heq])
   have z_Het_z_Hes: "bAll(bChoice(SUBSET(([''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)] \\ {})), (\<lambda>D. bAll(D, (\<lambda>a_d1a. bAll(D, (\<lambda>a_d2a. (((a_d1a[''slot''])=(a_d2a[''slot'']))=>(a_d1a=a_d2a)))))))), (\<lambda>x. (x \\in [''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)]))) == ?z_hes" (is "?z_het == _")
   by (unfold subset_def)
   have z_Het: "?z_het"
   by (unfold z_Het_z_Hes, fact z_Hes)
   have z_Hew_z_Het: "bAll((CHOOSE x:((x \\in SUBSET(([''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)] \\ {})))&bAll(x, (\<lambda>a_d1a. bAll(x, (\<lambda>a_d2a. (((a_d1a[''slot''])=(a_d2a[''slot'']))=>(a_d1a=a_d2a)))))))), (\<lambda>x. (x \\in [''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)]))) == ?z_het" (is "?z_hew == _")
   by (unfold bChoose_def)
   have z_Hew: "?z_hew"
   by (unfold z_Hew_z_Het, fact z_Het)
   have z_Hex_z_Hew: "(\\A x:((x \\in (CHOOSE x:((x \\in SUBSET(([''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)] \\ {})))&bAll(x, (\<lambda>a_d1a. bAll(x, (\<lambda>a_d2a. (((a_d1a[''slot''])=(a_d2a[''slot'']))=>(a_d1a=a_d2a)))))))))=>(x \\in [''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)]))) == ?z_hew" (is "?z_hex == _")
   by (unfold bAll_def)
   have z_Hex: "?z_hex" (is "\\A x : ?z_hez(x)")
   by (unfold z_Hex_z_Hew, fact z_Hew)
   have z_Hfa: "?z_hez((CHOOSE x:(~((x \\in (CHOOSE x:((x \\in SUBSET(([''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)] \\ {})))&bAll(x, (\<lambda>a_d1a. bAll(x, (\<lambda>a_d2a. (((a_d1a[''slot''])=(a_d2a[''slot'']))=>(a_d1a=a_d2a)))))))))=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(b, (x[''slot'']), (x[''val'']))))))"
   by (rule zenon_all_0 [of "?z_hez" "(CHOOSE x:(~((x \\in (CHOOSE x:((x \\in SUBSET(([''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)] \\ {})))&bAll(x, (\<lambda>a_d1a. bAll(x, (\<lambda>a_d2a. (((a_d1a[''slot''])=(a_d2a[''slot'']))=>(a_d1a=a_d2a)))))))))=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(b, (x[''slot'']), (x[''val''])))))", OF z_Hex])
   show FALSE
   proof (rule zenon_imply [OF z_Hfa])
    assume z_Hfb:"(~?z_hef)"
    show FALSE
    by (rule notE [OF z_Hfb z_Hef])
   next
    assume z_Hem:"?z_hem"
    show FALSE
    by (rule notE [OF z_Hel z_Hem])
   qed
  next
   assume z_Hfc:"((CHOOSE x:(~((x \\in (CHOOSE x:((x \\in SUBSET(([''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)] \\ {})))&bAll(x, (\<lambda>a_d1a. bAll(x, (\<lambda>a_d2a. (((a_d1a[''slot''])=(a_d2a[''slot'']))=>(a_d1a=a_d2a)))))))))=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(b, (x[''slot'']), (x[''val'']))))) \\in {})" (is "?z_hfc")
   show FALSE
   by (rule zenon_in_emptyset [of "(CHOOSE x:(~((x \\in (CHOOSE x:((x \\in SUBSET(([''slot'' : (FreeSlots(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))), ''val'' : (Values)] \\ {})))&bAll(x, (\<lambda>a_d1a. bAll(x, (\<lambda>a_d2a. (((a_d1a[''slot''])=(a_d2a[''slot'']))=>(a_d1a=a_d2a)))))))))=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(b, (x[''slot'']), (x[''val''])))))", OF z_Hfc])
  qed
 next
  assume z_Heg:"?z_heg"
  show FALSE
  by (rule notE [OF z_Heh z_Heg])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 296"; *} qed
lemma ob'306:
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Acceptors
fixes Values
fixes Quorums
fixes Proposers
fixes sent sent'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition voteds suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Bmax suppressed *)
(* usable definition FreeSlots suppressed *)
(* usable definition NewProposals suppressed *)
(* usable definition ProposeDecrees suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Preempt suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
assumes v'60: "(((((sent) \<in> ((SUBSET ((((((((([''type'' : ({(''1a'')}), ''bal'' : (Nat), ''from'' : (Proposers)]) \<union> ([''type'' : ({(''1b'')}), ''bal'' : (Nat), ''voted'' : ((SUBSET ([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)]))), ''from'' : (Acceptors)]))) \<union> ([''type'' : ({(''2a'')}), ''bal'' : (Nat), ''decrees'' : ((SUBSET ([''slot'' : (Nat), ''val'' : (Values)]))), ''from'' : (Proposers)]))) \<union> ([''type'' : ({(''2b'')}), ''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values), ''from'' : (Acceptors)]))) \<union> ([''type'' : ({(''preempt'')}), ''to'' : (Proposers), ''bal'' : (Nat)]))))))) \<and> (MsgInv)))"
assumes v'61: "(((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))"
fixes p
assumes p_in : "(p \<in> (Proposers))"
fixes m
assumes m_in : "(m \<in> ((a_senthash_primea :: c)))"
fixes b
assumes b_in : "(b \<in> (Nat))"
fixes Q
assumes Q_in : "(Q \<in> (Quorums))"
fixes S
assumes S_in : "(S \<in> ((SUBSET (sent))))"
assumes v'83: "(((~ (\<exists> a_m2a \<in> (sent) : (((((fapply ((a_m2a), (''type''))) = (''2a''))) \<and> (((fapply ((a_m2a), (''bal''))) = (b)))))))) & (((S) \<in> ((SUBSET (subsetOf((sent), %a_m2a. (((((fapply ((a_m2a), (''type''))) = (''1b''))) \<and> (((fapply ((a_m2a), (''bal''))) = (b))))))))))) & (\<forall> a \<in> (Q) : (\<exists> a_m2a \<in> (S) : (((fapply ((a_m2a), (''from''))) = (a))))) & ((Send (({(((''type'' :> (''2a'')) @@ (''bal'' :> (b)) @@ (''from'' :> (p)) @@ (''decrees'' :> ((ProposeDecrees (((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted'')))))))))))))})))))"
assumes v'90: "(((fapply ((m), (''type''))) = (''2a'')))"
fixes d
assumes d_in : "(d \<in> (subsetOf(((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted''))))))), %t. (\<forall> a_t1a \<in> ((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted''))))))) : (((((fapply ((a_t1a), (''slot''))) = (fapply ((t), (''slot''))))) \<Rightarrow> ((leq ((fapply ((a_t1a), (''bal''))), (fapply ((t), (''bal''))))))))))))"
fixes a_b2a
assumes a_b2a_in : "(a_b2a \<in> (Nat))"
assumes v'102: "(((a_b2a) \<in> ((isa_peri_peri_a (((0)), ((arith_add ((b), ((minus (((Succ[0])))))))))))))"
shows "(\<forall> a_d2a \<in> ((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted''))))))) : ((~ ((((~ ((leq ((fapply ((a_d2a), (''bal''))), (fapply ((d), (''bal'')))))))) \<and> (((fapply ((a_d2a), (''slot''))) = (fapply ((d), (''slot''))))))))))"(is "PROP ?ob'306")
proof -
ML_command {* writeln "*** TLAPS ENTER 306"; *}
show "PROP ?ob'306"

(* BEGIN ZENON INPUT
;; file=MultiPaxosUs.tlaps/tlapm_3daaf6.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >MultiPaxosUs.tlaps/tlapm_3daaf6.znn.out
;; obligation #306
$hyp "v'60" (/\ (TLA.in sent
(TLA.SUBSET (TLA.cup (TLA.cup (TLA.cup (TLA.cup (TLA.recordset "type" (TLA.set "1a") "bal" arith.N "from" Proposers)
(TLA.recordset "type" (TLA.set "1b") "bal" arith.N "voted" (TLA.SUBSET (TLA.recordset "bal" arith.N "slot" arith.N "val" Values)) "from" Acceptors))
(TLA.recordset "type" (TLA.set "2a") "bal" arith.N "decrees" (TLA.SUBSET (TLA.recordset "slot" arith.N "val" Values)) "from" Proposers))
(TLA.recordset "type" (TLA.set "2b") "bal" arith.N "slot" arith.N "val" Values "from" Acceptors))
(TLA.recordset "type" (TLA.set "preempt") "to" Proposers "bal" arith.N))))
MsgInv)
$hyp "v'61" (\/ Next (= a_h4fd5f73954dc53af536c1c75068837a
vars))
$hyp "p_in" (TLA.in p Proposers)
$hyp "m_in" (TLA.in m a_senthash_primea)
$hyp "b_in" (TLA.in b arith.N)
$hyp "Q_in" (TLA.in Q Quorums)
$hyp "S_in" (TLA.in S (TLA.SUBSET sent))
$hyp "v'83" (/\ (-. (TLA.bEx sent ((a_m2a) (/\ (= (TLA.fapply a_m2a "type")
"2a") (= (TLA.fapply a_m2a "bal") b))))) (TLA.in S
(TLA.SUBSET (TLA.subsetOf sent ((a_m2a) (/\ (= (TLA.fapply a_m2a "type")
"1b") (= (TLA.fapply a_m2a "bal") b))))))
(TLA.bAll Q ((a) (TLA.bEx S ((a_m2a) (= (TLA.fapply a_m2a "from") a)))))
(Send (TLA.set (TLA.record "type" "2a" "bal" b "from" p "decrees" (ProposeDecrees (TLA.UNION (TLA.setOfAll (TLA.subsetOf S ((m_1) (TLA.in (TLA.fapply m_1 "from")
Q))) ((m_1) (TLA.fapply m_1 "voted")))))))))
$hyp "v'90" (= (TLA.fapply m "type")
"2a")
$hyp "d_in" (TLA.in d (TLA.subsetOf (TLA.UNION (TLA.setOfAll (TLA.subsetOf S ((m_1) (TLA.in (TLA.fapply m_1 "from")
Q))) ((m_1) (TLA.fapply m_1 "voted")))) ((t) (TLA.bAll (TLA.UNION (TLA.setOfAll (TLA.subsetOf S ((m_1) (TLA.in (TLA.fapply m_1 "from")
Q))) ((m_1) (TLA.fapply m_1 "voted")))) ((a_t1a) (=> (= (TLA.fapply a_t1a "slot")
(TLA.fapply t "slot")) (arith.le (TLA.fapply a_t1a "bal")
(TLA.fapply t "bal"))))))))
$hyp "a_b2a_in" (TLA.in a_b2a arith.N)
$hyp "v'102" (TLA.in a_b2a (arith.intrange 0 (arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))))
$goal (TLA.bAll (TLA.UNION (TLA.setOfAll (TLA.subsetOf S ((m_1) (TLA.in (TLA.fapply m_1 "from")
Q))) ((m_1) (TLA.fapply m_1 "voted")))) ((a_d2a) (-. (/\ (-. (arith.le (TLA.fapply a_d2a "bal")
(TLA.fapply d "bal"))) (= (TLA.fapply a_d2a "slot")
(TLA.fapply d "slot"))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hj:"(d \\in subsetOf(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))), (\<lambda>t. bAll(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))), (\<lambda>a_t1a. (((a_t1a[''slot''])=(t[''slot'']))=>((a_t1a[''bal'']) <= (t[''bal'']))))))))" (is "?z_hj")
 using d_in by blast
 assume z_Hm:"(~bAll(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))), (\<lambda>a_d2a. (~((~((a_d2a[''bal'']) <= (d[''bal''])))&((a_d2a[''slot''])=(d[''slot''])))))))" (is "~?z_hbq")
 have z_Hcc: "bAll(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))), (\<lambda>a_t1a. (((a_t1a[''slot''])=(d[''slot'']))=>((a_t1a[''bal'']) <= (d[''bal''])))))" (is "?z_hcc")
 by (rule zenon_in_subsetof_1 [of "d" "UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))" "(\<lambda>t. bAll(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))), (\<lambda>a_t1a. (((a_t1a[''slot''])=(t[''slot'']))=>((a_t1a[''bal'']) <= (t[''bal'']))))))", OF z_Hj])
 have z_Hch_z_Hcc: "(\\A x:((x \\in UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))=>(((x[''slot''])=(d[''slot'']))=>((x[''bal'']) <= (d[''bal'']))))) == ?z_hcc" (is "?z_hch == _")
 by (unfold bAll_def)
 have z_Hch: "?z_hch" (is "\\A x : ?z_hcq(x)")
 by (unfold z_Hch_z_Hcc, fact z_Hcc)
 have z_Hcr_z_Hm: "(~(\\A x:((x \\in UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))=>(~((~((x[''bal'']) <= (d[''bal''])))&((x[''slot''])=(d[''slot'']))))))) == (~?z_hbq)" (is "?z_hcr == ?z_hm")
 by (unfold bAll_def)
 have z_Hcr: "?z_hcr" (is "~(\\A x : ?z_hcx(x))")
 by (unfold z_Hcr_z_Hm, fact z_Hm)
 have z_Hcy: "(\\E x:(~((x \\in UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))=>(~((~((x[''bal'']) <= (d[''bal''])))&((x[''slot''])=(d[''slot''])))))))" (is "\\E x : ?z_hda(x)")
 by (rule zenon_notallex_0 [of "?z_hcx", OF z_Hcr])
 have z_Hdb: "?z_hda((CHOOSE x:(~((x \\in UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))=>(~((~((x[''bal'']) <= (d[''bal''])))&((x[''slot''])=(d[''slot'']))))))))" (is "~(?z_hdd=>?z_hde)")
 by (rule zenon_ex_choose_0 [of "?z_hda", OF z_Hcy])
 have z_Hdd: "?z_hdd"
 by (rule zenon_notimply_0 [OF z_Hdb])
 have z_Hdf: "(~?z_hde)" (is "~~?z_hdg")
 by (rule zenon_notimply_1 [OF z_Hdb])
 have z_Hdg: "?z_hdg" (is "?z_hdh&?z_hdi")
 by (rule zenon_notnot_0 [OF z_Hdf])
 have z_Hdh: "?z_hdh" (is "~?z_hdj")
 by (rule zenon_and_0 [OF z_Hdg])
 have z_Hdi: "?z_hdi" (is "?z_hdk=?z_hcb")
 by (rule zenon_and_1 [OF z_Hdg])
 have z_Hdl: "?z_hcq((CHOOSE x:(~((x \\in UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))=>(~((~((x[''bal'']) <= (d[''bal''])))&((x[''slot''])=?z_hcb)))))))" (is "_=>?z_hdm")
 by (rule zenon_all_0 [of "?z_hcq" "(CHOOSE x:(~((x \\in UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))=>(~((~((x[''bal'']) <= (d[''bal''])))&((x[''slot''])=?z_hcb))))))", OF z_Hch])
 show FALSE
 proof (rule zenon_imply [OF z_Hdl])
  assume z_Hdn:"(~?z_hdd)"
  show FALSE
  by (rule notE [OF z_Hdn z_Hdd])
 next
  assume z_Hdm:"?z_hdm"
  show FALSE
  proof (rule zenon_imply [OF z_Hdm])
   assume z_Hdo:"(?z_hdk~=?z_hcb)"
   show FALSE
   by (rule notE [OF z_Hdo z_Hdi])
  next
   assume z_Hdj:"?z_hdj"
   show FALSE
   by (rule notE [OF z_Hdh z_Hdj])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 306"; *} qed
lemma ob'401:
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Acceptors
fixes Values
fixes Quorums
fixes Proposers
fixes sent sent'
(* usable definition vars suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition PartialBmax suppressed *)
(* usable definition voteds suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Bmax suppressed *)
(* usable definition FreeSlots suppressed *)
(* usable definition NewProposals suppressed *)
(* usable definition ProposeDecrees suppressed *)
(* usable definition VS suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Preempt suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
assumes v'63: "(((TypeOK) \<and> (MsgInv)))"
assumes v'64: "(((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))"
fixes p
assumes p_in : "(p \<in> (Proposers))"
fixes m
assumes m_in : "(m \<in> ((a_senthash_primea :: c)))"
fixes b
assumes b_in : "(b \<in> (Nat))"
fixes Q
assumes Q_in : "(Q \<in> (Quorums))"
fixes S
assumes S_in : "(S \<in> ((SUBSET (sent))))"
assumes v'86: "(((~ (\<exists> a_m2a \<in> (sent) : (((((fapply ((a_m2a), (''type''))) = (''2a''))) \<and> (((fapply ((a_m2a), (''bal''))) = (b)))))))) & (((S) \<in> ((SUBSET (subsetOf((sent), %a_m2a. (((((fapply ((a_m2a), (''type''))) = (''1b''))) \<and> (((fapply ((a_m2a), (''bal''))) = (b))))))))))) & (\<forall> a \<in> (Q) : (\<exists> a_m2a \<in> (S) : (((fapply ((a_m2a), (''from''))) = (a))))))"
assumes v'87: "((((a_senthash_primea :: c)) = (((sent) \<union> ({(((''type'' :> (''2a'')) @@ (''bal'' :> (b)) @@ (''from'' :> (p)) @@ (''decrees'' :> ((ProposeDecrees (((VS ((S), (Q))))))))))})))))"
assumes v'94: "(((fapply ((m), (''type''))) = (''2a'')))"
assumes v'106: "(((m) \<in> ((((a_senthash_primea :: c)) \\ (sent)))))"
assumes v'107: "(\<forall> a_m2a \<in> ((((a_senthash_primea :: c)) \\ (sent))) : (((((fapply ((a_m2a), (''type''))) = (''2a''))) \<and> (((fapply ((a_m2a), (''bal''))) = (b))))))"
assumes v'108: "(\<forall> a_m2a \<in> (sent) : (((((fapply ((a_m2a), (''type''))) = (''2a''))) \<Rightarrow> (((fapply ((a_m2a), (''bal''))) \<noteq> (b))))))"
shows "(\<forall> a_m2a \<in> ((a_senthash_primea :: c)) : (((((((fapply ((a_m2a), (''type''))) = (''2a''))) \<and> (((fapply ((a_m2a), (''bal''))) = (fapply ((m), (''bal''))))))) \<Rightarrow> (((a_m2a) = (m))))))"(is "PROP ?ob'401")
proof -
ML_command {* writeln "*** TLAPS ENTER 401"; *}
show "PROP ?ob'401"

(* BEGIN ZENON INPUT
;; file=MultiPaxosUs.tlaps/tlapm_09e7c2.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >MultiPaxosUs.tlaps/tlapm_09e7c2.znn.out
;; obligation #401
$hyp "v'63" (/\ TypeOK MsgInv)
$hyp "v'64" (\/ Next (= a_h4fd5f73954dc53af536c1c75068837a
vars))
$hyp "p_in" (TLA.in p Proposers)
$hyp "m_in" (TLA.in m a_senthash_primea)
$hyp "b_in" (TLA.in b arith.N)
$hyp "Q_in" (TLA.in Q Quorums)
$hyp "S_in" (TLA.in S (TLA.SUBSET sent))
$hyp "v'86" (/\ (-. (TLA.bEx sent ((a_m2a) (/\ (= (TLA.fapply a_m2a "type")
"2a") (= (TLA.fapply a_m2a "bal") b))))) (TLA.in S
(TLA.SUBSET (TLA.subsetOf sent ((a_m2a) (/\ (= (TLA.fapply a_m2a "type")
"1b") (= (TLA.fapply a_m2a "bal") b))))))
(TLA.bAll Q ((a) (TLA.bEx S ((a_m2a) (= (TLA.fapply a_m2a "from")
a))))))
$hyp "v'87" (= a_senthash_primea (TLA.cup sent
(TLA.set (TLA.record "type" "2a" "bal" b "from" p "decrees" (ProposeDecrees (VS S
Q))))))
$hyp "v'94" (= (TLA.fapply m "type") "2a")
$hyp "v'106" (TLA.in m (TLA.setminus a_senthash_primea
sent))
$hyp "v'107" (TLA.bAll (TLA.setminus a_senthash_primea
sent) ((a_m2a) (/\ (= (TLA.fapply a_m2a "type") "2a")
(= (TLA.fapply a_m2a "bal")
b))))
$hyp "v'108" (TLA.bAll sent ((a_m2a) (=> (= (TLA.fapply a_m2a "type") "2a")
(-. (= (TLA.fapply a_m2a "bal")
b)))))
$goal (TLA.bAll a_senthash_primea ((a_m2a) (=> (/\ (= (TLA.fapply a_m2a "type")
"2a") (= (TLA.fapply a_m2a "bal") (TLA.fapply m "bal"))) (= a_m2a
m))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hi:"(a_senthash_primea=(sent \\cup {(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''from'' :> (p) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))}))" (is "_=?z_hp")
 using v'87 by blast
 have z_Hd:"(m \\in a_senthash_primea)" (is "?z_hd")
 using m_in by blast
 have z_Hk:"(m \\in (a_senthash_primea \\ sent))" (is "?z_hk")
 using v'106 by blast
 have z_Hl:"bAll((a_senthash_primea \\ sent), (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=b))))" (is "?z_hl")
 using v'107 by blast
 have z_Hm:"bAll(sent, (\<lambda>a_m2a. (((a_m2a[''type''])=''2a'')=>((a_m2a[''bal''])~=b))))" (is "?z_hm")
 using v'108 by blast
 assume z_Hn:"(~bAll(a_senthash_primea, (\<lambda>a_m2a. ((((a_m2a[''type''])=''2a'')&((a_m2a[''bal''])=(m[''bal''])))=>(a_m2a=m)))))" (is "~?z_hbq")
 have z_Hd: "?z_hd"
 by (rule zenon_in_setminus_0 [of "m" "a_senthash_primea" "sent", OF z_Hk])
 have z_Hbx: "(~(m \\in sent))" (is "~?z_hby")
 by (rule zenon_in_setminus_1 [of "m" "a_senthash_primea" "sent", OF z_Hk])
 have z_Hbz_z_Hm: "(\\A x:((x \\in sent)=>(((x[''type''])=''2a'')=>((x[''bal''])~=b)))) == ?z_hm" (is "?z_hbz == _")
 by (unfold bAll_def)
 have z_Hbz: "?z_hbz" (is "\\A x : ?z_hci(x)")
 by (unfold z_Hbz_z_Hm, fact z_Hm)
 have z_Hcj_z_Hn: "(~(\\A x:((x \\in a_senthash_primea)=>((((x[''type''])=''2a'')&((x[''bal''])=(m[''bal''])))=>(x=m))))) == (~?z_hbq)" (is "?z_hcj == ?z_hn")
 by (unfold bAll_def)
 have z_Hcj: "?z_hcj" (is "~(\\A x : ?z_hcr(x))")
 by (unfold z_Hcj_z_Hn, fact z_Hn)
 have z_Hcs: "(\\E x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''2a'')&((x[''bal''])=(m[''bal''])))=>(x=m)))))" (is "\\E x : ?z_hcu(x)")
 by (rule zenon_notallex_0 [of "?z_hcr", OF z_Hcj])
 have z_Hcv: "?z_hcu((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''2a'')&((x[''bal''])=(m[''bal''])))=>(x=m))))))" (is "~(?z_hcx=>?z_hcy)")
 by (rule zenon_ex_choose_0 [of "?z_hcu", OF z_Hcs])
 have z_Hcx: "?z_hcx"
 by (rule zenon_notimply_0 [OF z_Hcv])
 have z_Hcz: "(~?z_hcy)" (is "~(?z_hda=>?z_hdb)")
 by (rule zenon_notimply_1 [OF z_Hcv])
 have z_Hda: "?z_hda" (is "?z_hdc&?z_hdd")
 by (rule zenon_notimply_0 [OF z_Hcz])
 have z_Hde: "((CHOOSE x:(~((x \\in a_senthash_primea)=>((((x[''type''])=''2a'')&((x[''bal''])=(m[''bal''])))=>(x=m)))))~=m)" (is "?z_hcw~=_")
 by (rule zenon_notimply_1 [OF z_Hcz])
 have z_Hdc: "?z_hdc" (is "?z_hdf=?z_hu")
 by (rule zenon_and_0 [OF z_Hda])
 have z_Hdd: "?z_hdd" (is "?z_hdg=?z_hbv")
 by (rule zenon_and_1 [OF z_Hda])
 have z_Hdh: "(?z_hcw \\in ?z_hp)" (is "?z_hdh")
 by (rule subst [where P="(\<lambda>zenon_Vnia. (?z_hcw \\in zenon_Vnia))", OF z_Hi z_Hcx])
 show FALSE
 proof (rule zenon_in_cup [of "?z_hcw" "sent" "{(''type'' :> (?z_hu) @@ ''bal'' :> (b) @@ ''from'' :> (p) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))}", OF z_Hdh])
  assume z_Hdl:"(?z_hcw \\in sent)" (is "?z_hdl")
  have z_Hdm: "?z_hci(?z_hcw)" (is "_=>?z_hdn")
  by (rule zenon_all_0 [of "?z_hci" "?z_hcw", OF z_Hbz])
  show FALSE
  proof (rule zenon_imply [OF z_Hdm])
   assume z_Hdo:"(~?z_hdl)"
   show FALSE
   by (rule notE [OF z_Hdo z_Hdl])
  next
   assume z_Hdn:"?z_hdn" (is "_=>?z_hdp")
   show FALSE
   proof (rule zenon_imply [OF z_Hdn])
    assume z_Hdq:"(?z_hdf~=?z_hu)"
    show FALSE
    by (rule notE [OF z_Hdq z_Hdc])
   next
    assume z_Hdp:"?z_hdp"
    have z_Hdr: "(((m[''type''])=?z_hu)&(?z_hbv=b))" (is "?z_hj&?z_hdt")
    by (rule zenon_all_in_0 [of "(a_senthash_primea \\ sent)" "(\<lambda>a_m2a. (((a_m2a[''type''])=?z_hu)&((a_m2a[''bal''])=b)))", OF z_Hl z_Hk])
    have z_Hdt: "?z_hdt"
    by (rule zenon_and_1 [OF z_Hdr])
    show FALSE
    proof (rule notE [OF z_Hdp])
     have z_Hdu: "(?z_hdg=b)"
     by (rule subst [where P="(\<lambda>zenon_Vqia. (?z_hdg=zenon_Vqia))", OF z_Hdt], fact z_Hdd)
     thus "(?z_hdg=b)" .
    qed
   qed
  qed
 next
  assume z_Hdy:"(?z_hcw \\in {(''type'' :> (?z_hu) @@ ''bal'' :> (b) @@ ''from'' :> (p) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))})" (is "?z_hdy")
  show FALSE
  proof (rule zenon_in_addElt [of "?z_hcw" "(''type'' :> (?z_hu) @@ ''bal'' :> (b) @@ ''from'' :> (p) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q))))" "{}", OF z_Hdy])
   assume z_Hea:"(?z_hcw=(''type'' :> (?z_hu) @@ ''bal'' :> (b) @@ ''from'' :> (p) @@ ''decrees'' :> (ProposeDecrees(VS(S, Q)))))" (is "_=?z_hs")
   have z_Heb: "(m \\in ?z_hp)" (is "?z_heb")
   by (rule subst [where P="(\<lambda>zenon_Vpia. (m \\in zenon_Vpia))", OF z_Hi z_Hd])
   show FALSE
   proof (rule zenon_in_cup [of "m" "sent" "{?z_hs}", OF z_Heb])
    assume z_Hby:"?z_hby"
    show FALSE
    by (rule notE [OF z_Hbx z_Hby])
   next
    assume z_Hef:"(m \\in {?z_hs})" (is "?z_hef")
    show FALSE
    proof (rule zenon_in_addElt [of "m" "?z_hs" "{}", OF z_Hef])
     assume z_Heg:"(m=?z_hs)"
     show FALSE
     proof (rule notE [OF z_Hde])
      have z_Heh: "(?z_hs=m)"
      by (rule sym [OF z_Heg])
      have z_Hdb: "?z_hdb"
      by (rule subst [where P="(\<lambda>zenon_Vria. (?z_hcw=zenon_Vria))", OF z_Heh], fact z_Hea)
      thus "?z_hdb" .
     qed
    next
     assume z_Hel:"(m \\in {})" (is "?z_hel")
     show FALSE
     by (rule zenon_in_emptyset [of "m", OF z_Hel])
    qed
   qed
  next
   assume z_Hem:"(?z_hcw \\in {})" (is "?z_hem")
   show FALSE
   by (rule zenon_in_emptyset [of "?z_hcw", OF z_Hem])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 401"; *} qed
lemma ob'385:
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Acceptors
fixes Values
fixes Quorums
fixes Proposers
fixes sent sent'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition PartialBmax suppressed *)
(* usable definition voteds suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Bmax suppressed *)
(* usable definition FreeSlots suppressed *)
(* usable definition NewProposals suppressed *)
(* usable definition ProposeDecrees suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Preempt suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
assumes v'63: "(((TypeOK) \<and> (MsgInv)))"
assumes v'64: "(((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))"
fixes p
assumes p_in : "(p \<in> (Proposers))"
fixes m
assumes m_in : "(m \<in> ((a_senthash_primea :: c)))"
fixes b
assumes b_in : "(b \<in> (Nat))"
fixes Q
assumes Q_in : "(Q \<in> (Quorums))"
fixes S
assumes S_in : "(S \<in> ((SUBSET (sent))))"
assumes v'86: "(((~ (\<exists> a_m2a \<in> (sent) : (((((fapply ((a_m2a), (''type''))) = (''2a''))) \<and> (((fapply ((a_m2a), (''bal''))) = (b)))))))) & (((S) \<in> ((SUBSET (subsetOf((sent), %a_m2a. (((((fapply ((a_m2a), (''type''))) = (''1b''))) \<and> (((fapply ((a_m2a), (''bal''))) = (b))))))))))) & (\<forall> a \<in> (Q) : (\<exists> a_m2a \<in> (S) : (((fapply ((a_m2a), (''from''))) = (a))))) & ((Send (({(((''type'' :> (''2a'')) @@ (''bal'' :> (b)) @@ (''from'' :> (p)) @@ (''decrees'' :> ((ProposeDecrees (((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted'')))))))))))))})))))"
assumes v'93: "(((fapply ((m), (''type''))) = (''2a'')))"
assumes v'107: "(\<forall> a_r1a \<in> ((PartialBmax (((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted'')))))))))) : (\<forall> a_r2a \<in> ((PartialBmax (((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted'')))))))))) : (((((((fapply ((a_r1a), (''bal''))) = (fapply ((a_r2a), (''bal''))))) \<and> (((fapply ((a_r1a), (''slot''))) = (fapply ((a_r2a), (''slot''))))))) \<Rightarrow> (((fapply ((a_r1a), (''val''))) = (fapply ((a_r2a), (''val'')))))))))"
assumes v'108: "(\<forall> a_r1a \<in> ((PartialBmax (((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted'')))))))))) : (\<forall> a_r2a \<in> ((PartialBmax (((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted'')))))))))) : (((((fapply ((a_r1a), (''slot''))) = (fapply ((a_r2a), (''slot''))))) \<Rightarrow> (((fapply ((a_r1a), (''bal''))) = (fapply ((a_r2a), (''bal'')))))))))"
assumes v'109: "((((PartialBmax (((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted'')))))))))) \<subseteq> ((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted'')))))))))"
assumes v'110: "((((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted''))))))) \<in> ((SUBSET ([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])))))"
shows "(\<forall> a_r1a \<in> ((PartialBmax (((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted'')))))))))) : (\<forall> a_r2a \<in> ((PartialBmax (((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted'')))))))))) : (((((fapply ((a_r1a), (''slot''))) = (fapply ((a_r2a), (''slot''))))) \<Rightarrow> (((((fapply ((a_r1a), (''bal''))) = (fapply ((a_r2a), (''bal''))))) \<and> (((fapply ((a_r1a), (''val''))) = (fapply ((a_r2a), (''val'')))))))))))"(is "PROP ?ob'385")
proof -
ML_command {* writeln "*** TLAPS ENTER 385"; *}
show "PROP ?ob'385"

(* BEGIN ZENON INPUT
;; file=MultiPaxosUs.tlaps/tlapm_e36156.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >MultiPaxosUs.tlaps/tlapm_e36156.znn.out
;; obligation #385
$hyp "v'63" (/\ TypeOK MsgInv)
$hyp "v'64" (\/ Next (= a_h4fd5f73954dc53af536c1c75068837a
vars))
$hyp "p_in" (TLA.in p Proposers)
$hyp "m_in" (TLA.in m a_senthash_primea)
$hyp "b_in" (TLA.in b arith.N)
$hyp "Q_in" (TLA.in Q Quorums)
$hyp "S_in" (TLA.in S (TLA.SUBSET sent))
$hyp "v'86" (/\ (-. (TLA.bEx sent ((a_m2a) (/\ (= (TLA.fapply a_m2a "type")
"2a") (= (TLA.fapply a_m2a "bal") b))))) (TLA.in S
(TLA.SUBSET (TLA.subsetOf sent ((a_m2a) (/\ (= (TLA.fapply a_m2a "type")
"1b") (= (TLA.fapply a_m2a "bal") b))))))
(TLA.bAll Q ((a) (TLA.bEx S ((a_m2a) (= (TLA.fapply a_m2a "from") a)))))
(Send (TLA.set (TLA.record "type" "2a" "bal" b "from" p "decrees" (ProposeDecrees (TLA.UNION (TLA.setOfAll (TLA.subsetOf S ((m_1) (TLA.in (TLA.fapply m_1 "from")
Q))) ((m_1) (TLA.fapply m_1 "voted")))))))))
$hyp "v'93" (= (TLA.fapply m "type")
"2a")
$hyp "v'107" (TLA.bAll (PartialBmax (TLA.UNION (TLA.setOfAll (TLA.subsetOf S ((m_1) (TLA.in (TLA.fapply m_1 "from")
Q))) ((m_1) (TLA.fapply m_1 "voted"))))) ((a_r1a) (TLA.bAll (PartialBmax (TLA.UNION (TLA.setOfAll (TLA.subsetOf S ((m_1) (TLA.in (TLA.fapply m_1 "from")
Q))) ((m_1) (TLA.fapply m_1 "voted"))))) ((a_r2a) (=> (/\ (= (TLA.fapply a_r1a "bal")
(TLA.fapply a_r2a "bal")) (= (TLA.fapply a_r1a "slot")
(TLA.fapply a_r2a "slot"))) (= (TLA.fapply a_r1a "val")
(TLA.fapply a_r2a "val")))))))
$hyp "v'108" (TLA.bAll (PartialBmax (TLA.UNION (TLA.setOfAll (TLA.subsetOf S ((m_1) (TLA.in (TLA.fapply m_1 "from")
Q))) ((m_1) (TLA.fapply m_1 "voted"))))) ((a_r1a) (TLA.bAll (PartialBmax (TLA.UNION (TLA.setOfAll (TLA.subsetOf S ((m_1) (TLA.in (TLA.fapply m_1 "from")
Q))) ((m_1) (TLA.fapply m_1 "voted"))))) ((a_r2a) (=> (= (TLA.fapply a_r1a "slot")
(TLA.fapply a_r2a "slot")) (= (TLA.fapply a_r1a "bal")
(TLA.fapply a_r2a "bal")))))))
$hyp "v'109" (TLA.subseteq (PartialBmax (TLA.UNION (TLA.setOfAll (TLA.subsetOf S ((m_1) (TLA.in (TLA.fapply m_1 "from")
Q))) ((m_1) (TLA.fapply m_1 "voted")))))
(TLA.UNION (TLA.setOfAll (TLA.subsetOf S ((m_1) (TLA.in (TLA.fapply m_1 "from")
Q))) ((m_1) (TLA.fapply m_1 "voted")))))
$hyp "v'110" (TLA.in (TLA.UNION (TLA.setOfAll (TLA.subsetOf S ((m_1) (TLA.in (TLA.fapply m_1 "from")
Q))) ((m_1) (TLA.fapply m_1 "voted"))))
(TLA.SUBSET (TLA.recordset "bal" arith.N "slot" arith.N "val" Values)))
$goal (TLA.bAll (PartialBmax (TLA.UNION (TLA.setOfAll (TLA.subsetOf S ((m_1) (TLA.in (TLA.fapply m_1 "from")
Q))) ((m_1) (TLA.fapply m_1 "voted"))))) ((a_r1a) (TLA.bAll (PartialBmax (TLA.UNION (TLA.setOfAll (TLA.subsetOf S ((m_1) (TLA.in (TLA.fapply m_1 "from")
Q))) ((m_1) (TLA.fapply m_1 "voted"))))) ((a_r2a) (=> (= (TLA.fapply a_r1a "slot")
(TLA.fapply a_r2a "slot")) (/\ (= (TLA.fapply a_r1a "bal")
(TLA.fapply a_r2a "bal")) (= (TLA.fapply a_r1a "val")
(TLA.fapply a_r2a "val"))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hj:"bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r1a. bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. ((((a_r1a[''bal''])=(a_r2a[''bal'']))&((a_r1a[''slot''])=(a_r2a[''slot''])))=>((a_r1a[''val''])=(a_r2a[''val''])))))))" (is "?z_hj")
 using v'107 by blast
 have z_Hk:"bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r1a. bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((a_r1a[''slot''])=(a_r2a[''slot'']))=>((a_r1a[''bal''])=(a_r2a[''bal''])))))))" (is "?z_hk")
 using v'108 by blast
 assume z_Hn:"(~bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r1a. bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((a_r1a[''slot''])=(a_r2a[''slot'']))=>(((a_r1a[''bal''])=(a_r2a[''bal'']))&((a_r1a[''val''])=(a_r2a[''val''])))))))))" (is "~?z_hbz")
 have z_Hcf_z_Hj: "(\\A x:((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. ((((x[''bal''])=(a_r2a[''bal'']))&((x[''slot''])=(a_r2a[''slot''])))=>((x[''val''])=(a_r2a[''val'']))))))) == ?z_hj" (is "?z_hcf == _")
 by (unfold bAll_def)
 have z_Hcf: "?z_hcf" (is "\\A x : ?z_hct(x)")
 by (unfold z_Hcf_z_Hj, fact z_Hj)
 have z_Hcu_z_Hk: "(\\A x:((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>((x[''bal''])=(a_r2a[''bal'']))))))) == ?z_hk" (is "?z_hcu == _")
 by (unfold bAll_def)
 have z_Hcu: "?z_hcu" (is "\\A x : ?z_hcz(x)")
 by (unfold z_Hcu_z_Hk, fact z_Hk)
 have z_Hda_z_Hn: "(~(\\A x:((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val'']))))))))) == (~?z_hbz)" (is "?z_hda == ?z_hn")
 by (unfold bAll_def)
 have z_Hda: "?z_hda" (is "~(\\A x : ?z_hdh(x))")
 by (unfold z_Hda_z_Hn, fact z_Hn)
 have z_Hdi: "(\\E x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))" (is "\\E x : ?z_hdk(x)")
 by (rule zenon_notallex_0 [of "?z_hdh", OF z_Hda])
 have z_Hdl: "?z_hdk((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val'']))))))))))" (is "~(?z_hdn=>?z_hdo)")
 by (rule zenon_ex_choose_0 [of "?z_hdk", OF z_Hdi])
 have z_Hdn: "?z_hdn"
 by (rule zenon_notimply_0 [OF z_Hdl])
 have z_Hdp: "(~?z_hdo)"
 by (rule zenon_notimply_1 [OF z_Hdl])
 have z_Hdq_z_Hdp: "(~(\\A x:((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>((((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))[''slot''])=(x[''slot'']))=>((((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))[''bal''])=(x[''bal'']))&(((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))[''val''])=(x[''val'']))))))) == (~?z_hdo)" (is "?z_hdq == ?z_hdp")
 by (unfold bAll_def)
 have z_Hdq: "?z_hdq" (is "~(\\A x : ?z_heb(x))")
 by (unfold z_Hdq_z_Hdp, fact z_Hdp)
 have z_Hec: "(\\E x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>((((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))[''slot''])=(x[''slot'']))=>((((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))[''bal''])=(x[''bal'']))&(((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))[''val''])=(x[''val''])))))))" (is "\\E x : ?z_hee(x)")
 by (rule zenon_notallex_0 [of "?z_heb", OF z_Hdq])
 have z_Hef: "?z_hee((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>((((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))[''slot''])=(x[''slot'']))=>((((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))[''bal''])=(x[''bal'']))&(((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))[''val''])=(x[''val'']))))))))" (is "~(?z_heh=>?z_hei)")
 by (rule zenon_ex_choose_0 [of "?z_hee", OF z_Hec])
 have z_Heh: "?z_heh"
 by (rule zenon_notimply_0 [OF z_Hef])
 have z_Hej: "(~?z_hei)" (is "~(?z_hek=>?z_hel)")
 by (rule zenon_notimply_1 [OF z_Hef])
 have z_Hek: "?z_hek" (is "?z_hdv=?z_hem")
 by (rule zenon_notimply_0 [OF z_Hej])
 have z_Hen: "(~?z_hel)" (is "~(?z_heo&?z_hep)")
 by (rule zenon_notimply_1 [OF z_Hej])
 show FALSE
 proof (rule zenon_notand [OF z_Hen])
  assume z_Heq:"(((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))[''bal''])~=((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>((?z_hdv=(x[''slot'']))=>((((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))[''bal''])=(x[''bal'']))&(((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))[''val''])=(x[''val''])))))))[''bal'']))" (is "?z_hdy~=?z_her")
  have z_Hes: "?z_hcz((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>((?z_hdv=(x[''slot'']))=>((?z_hdy=(x[''bal'']))&(((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))[''val''])=(x[''val'']))))))))" (is "_=>?z_het")
  by (rule zenon_all_0 [of "?z_hcz" "(CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>((?z_hdv=(x[''slot'']))=>((?z_hdy=(x[''bal'']))&(((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))[''val''])=(x[''val''])))))))", OF z_Hcu])
  show FALSE
  proof (rule zenon_imply [OF z_Hes])
   assume z_Heu:"(~?z_heh)"
   show FALSE
   by (rule notE [OF z_Heu z_Heh])
  next
   assume z_Het:"?z_het"
   have z_Hev_z_Het: "(\\A x:((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>((?z_hem=(x[''slot'']))=>(?z_her=(x[''bal'']))))) == ?z_het" (is "?z_hev == _")
   by (unfold bAll_def)
   have z_Hev: "?z_hev" (is "\\A x : ?z_hfa(x)")
   by (unfold z_Hev_z_Het, fact z_Het)
   have z_Hfb: "?z_hfa((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val'']))))))))))" (is "_=>?z_hfc")
   by (rule zenon_all_0 [of "?z_hfa" "(CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))", OF z_Hev])
   show FALSE
   proof (rule zenon_imply [OF z_Hfb])
    assume z_Hfd:"(~?z_hdn)"
    show FALSE
    by (rule notE [OF z_Hfd z_Hdn])
   next
    assume z_Hfc:"?z_hfc" (is "?z_hfe=>?z_hff")
    show FALSE
    proof (rule zenon_imply [OF z_Hfc])
     assume z_Hfg:"(?z_hem~=?z_hdv)"
     show FALSE
     by (rule zenon_eqsym [OF z_Hek z_Hfg])
    next
     assume z_Hff:"?z_hff"
     show FALSE
     by (rule zenon_eqsym [OF z_Hff z_Heq])
    qed
   qed
  qed
 next
  assume z_Hfh:"(((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))[''val''])~=((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>((?z_hdv=(x[''slot'']))=>((((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))[''bal''])=(x[''bal'']))&(((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))[''val''])=(x[''val''])))))))[''val'']))" (is "?z_hea~=?z_hfi")
  have z_Hfj: "?z_hct((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>((?z_hdv=(x[''slot'']))=>((((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))[''bal''])=(x[''bal'']))&(?z_hea=(x[''val'']))))))))" (is "_=>?z_hfk")
  by (rule zenon_all_0 [of "?z_hct" "(CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>((?z_hdv=(x[''slot'']))=>((((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))[''bal''])=(x[''bal'']))&(?z_hea=(x[''val''])))))))", OF z_Hcf])
  show FALSE
  proof (rule zenon_imply [OF z_Hfj])
   assume z_Heu:"(~?z_heh)"
   show FALSE
   by (rule notE [OF z_Heu z_Heh])
  next
   assume z_Hfk:"?z_hfk"
   have z_Hfl_z_Hfk: "(\\A x:((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>(((((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>((?z_hdv=(x[''slot'']))=>((((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))[''bal''])=(x[''bal'']))&(?z_hea=(x[''val''])))))))[''bal''])=(x[''bal'']))&(?z_hem=(x[''slot''])))=>(?z_hfi=(x[''val'']))))) == ?z_hfk" (is "?z_hfl == _")
   by (unfold bAll_def)
   have z_Hfl: "?z_hfl" (is "\\A x : ?z_hfq(x)")
   by (unfold z_Hfl_z_Hfk, fact z_Hfk)
   have z_Hfr: "bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. ((?z_hdv=(a_r2a[''slot'']))=>(((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))[''bal''])=(a_r2a[''bal''])))))" (is "?z_hfr")
   by (rule zenon_all_in_0 [of "PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))" "(\<lambda>a_r1a. bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((a_r1a[''slot''])=(a_r2a[''slot'']))=>((a_r1a[''bal''])=(a_r2a[''bal'']))))))", OF z_Hk z_Hdn])
   have z_Hfw: "?z_hfq((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val'']))))))))))" (is "_=>?z_hfx")
   by (rule zenon_all_0 [of "?z_hfq" "(CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))", OF z_Hfl])
   show FALSE
   proof (rule zenon_imply [OF z_Hfw])
    assume z_Hfd:"(~?z_hdn)"
    show FALSE
    by (rule notE [OF z_Hfd z_Hdn])
   next
    assume z_Hfx:"?z_hfx" (is "?z_hfy=>?z_hfz")
    show FALSE
    proof (rule zenon_imply [OF z_Hfx])
     assume z_Hga:"(~?z_hfy)" (is "~(?z_hff&?z_hfe)")
     show FALSE
     proof (rule zenon_notand [OF z_Hga])
      assume z_Hgb:"(((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>((?z_hdv=(x[''slot'']))=>((((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))[''bal''])=(x[''bal'']))&(?z_hea=(x[''val''])))))))[''bal''])~=((CHOOSE x:(~((x \\in PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))))=>bAll(PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted'']))))), (\<lambda>a_r2a. (((x[''slot''])=(a_r2a[''slot'']))=>(((x[''bal''])=(a_r2a[''bal'']))&((x[''val''])=(a_r2a[''val''])))))))))[''bal'']))" (is "?z_her~=?z_hdy")
      have z_Hgc: "(?z_hek=>?z_heo)"
      by (rule zenon_all_in_0 [of "PartialBmax(UNION(setOfAll(subsetOf(S, (\<lambda>m_1. ((m_1[''from'']) \\in Q))), (\<lambda>m_1. (m_1[''voted''])))))" "(\<lambda>a_r2a. ((?z_hdv=(a_r2a[''slot'']))=>(?z_hdy=(a_r2a[''bal'']))))", OF z_Hfr z_Heh])
      show FALSE
      proof (rule zenon_imply [OF z_Hgc])
       assume z_Hgd:"(?z_hdv~=?z_hem)"
       show FALSE
       by (rule notE [OF z_Hgd z_Hek])
      next
       assume z_Heo:"?z_heo"
       show FALSE
       by (rule zenon_eqsym [OF z_Heo z_Hgb])
      qed
     next
      assume z_Hfg:"(?z_hem~=?z_hdv)"
      show FALSE
      by (rule zenon_eqsym [OF z_Hek z_Hfg])
     qed
    next
     assume z_Hfz:"?z_hfz"
     show FALSE
     by (rule zenon_eqsym [OF z_Hfz z_Hfh])
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 385"; *} qed
lemma ob'390:
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Acceptors
fixes Values
fixes Quorums
fixes Proposers
fixes sent sent'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition PartialBmax suppressed *)
(* usable definition voteds suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition FreeSlots suppressed *)
(* usable definition NewProposals suppressed *)
(* usable definition ProposeDecrees suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Preempt suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
assumes v'62: "(((TypeOK) \<and> (MsgInv)))"
assumes v'63: "(((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))"
fixes p
assumes p_in : "(p \<in> (Proposers))"
fixes m
assumes m_in : "(m \<in> ((a_senthash_primea :: c)))"
fixes b
assumes b_in : "(b \<in> (Nat))"
fixes Q
assumes Q_in : "(Q \<in> (Quorums))"
fixes S
assumes S_in : "(S \<in> ((SUBSET (sent))))"
assumes v'85: "(((~ (\<exists> a_m2a \<in> (sent) : (((((fapply ((a_m2a), (''type''))) = (''2a''))) \<and> (((fapply ((a_m2a), (''bal''))) = (b)))))))) & (((S) \<in> ((SUBSET (subsetOf((sent), %a_m2a. (((((fapply ((a_m2a), (''type''))) = (''1b''))) \<and> (((fapply ((a_m2a), (''bal''))) = (b))))))))))) & (\<forall> a \<in> (Q) : (\<exists> a_m2a \<in> (S) : (((fapply ((a_m2a), (''from''))) = (a))))) & ((Send (({(((''type'' :> (''2a'')) @@ (''bal'' :> (b)) @@ (''from'' :> (p)) @@ (''decrees'' :> ((ProposeDecrees (((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted'')))))))))))))})))))"
assumes v'92: "(((fapply ((m), (''type''))) = (''2a'')))"
assumes v'107: "(\<forall> a_r1a \<in> ((PartialBmax (((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted'')))))))))) : (\<forall> a_r2a \<in> ((PartialBmax (((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted'')))))))))) : (((((fapply ((a_r1a), (''slot''))) = (fapply ((a_r2a), (''slot''))))) \<Rightarrow> (((((fapply ((a_r1a), (''bal''))) = (fapply ((a_r2a), (''bal''))))) \<and> (((fapply ((a_r1a), (''val''))) = (fapply ((a_r2a), (''val'')))))))))))"
shows "(\<forall> a_r1a \<in> (setOfAll(((PartialBmax (((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted'')))))))))), %t. (((''slot'' :> (fapply ((t), (''slot'')))) @@ (''val'' :> (fapply ((t), (''val'')))))))) : (\<forall> a_r2a \<in> (setOfAll(((PartialBmax (((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted'')))))))))), %t. (((''slot'' :> (fapply ((t), (''slot'')))) @@ (''val'' :> (fapply ((t), (''val'')))))))) : (((((fapply ((a_r1a), (''slot''))) = (fapply ((a_r2a), (''slot''))))) \<Rightarrow> (((a_r1a) = (a_r2a)))))))"(is "PROP ?ob'390")
proof -
ML_command {* writeln "*** TLAPS ENTER 390"; *}
show "PROP ?ob'390"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 390"; *} qed
lemma ob'350:
(* usable definition PropositionalTemporalLogic suppressed *)
fixes Acceptors
fixes Values
fixes Quorums
fixes Proposers
fixes sent sent'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition PartialBmax suppressed *)
(* usable definition voteds suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition FreeSlots suppressed *)
(* usable definition NewProposals suppressed *)
(* usable definition ProposeDecrees suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Preempt suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
assumes v'62: "(((TypeOK) \<and> (MsgInv)))"
assumes v'63: "(((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))"
fixes p
assumes p_in : "(p \<in> (Proposers))"
fixes m
assumes m_in : "(m \<in> ((a_senthash_primea :: c)))"
fixes b
assumes b_in : "(b \<in> (Nat))"
fixes Q
assumes Q_in : "(Q \<in> (Quorums))"
fixes S
assumes S_in : "(S \<in> ((SUBSET (sent))))"
assumes v'85: "(((~ (\<exists> a_m2a \<in> (sent) : (((((fapply ((a_m2a), (''type''))) = (''2a''))) \<and> (((fapply ((a_m2a), (''bal''))) = (b)))))))) & (((S) \<in> ((SUBSET (subsetOf((sent), %a_m2a. (((((fapply ((a_m2a), (''type''))) = (''1b''))) \<and> (((fapply ((a_m2a), (''bal''))) = (b))))))))))) & (\<forall> a \<in> (Q) : (\<exists> a_m2a \<in> (S) : (((fapply ((a_m2a), (''from''))) = (a))))) & ((Send (({(((''type'' :> (''2a'')) @@ (''bal'' :> (b)) @@ (''from'' :> (p)) @@ (''decrees'' :> ((ProposeDecrees (((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted'')))))))))))))})))))"
assumes v'92: "(((fapply ((m), (''type''))) = (''2a'')))"
assumes v'105: "(\<forall> d \<in> ((PartialBmax (((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted'')))))))))) : ((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((b), (fapply ((d), (''slot''))), (fapply ((d), (''val'')))) :: c)))"
assumes v'106: "((((PartialBmax (((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted'')))))))))) \<in> ((SUBSET ([''bal'' : (Nat), ''slot'' : (Nat), ''val'' : (Values)])))))"
shows "(\<forall> d \<in> (setOfAll(((PartialBmax (((UNION (setOfAll((subsetOf((S), %m_1. (((fapply ((m_1), (''from''))) \<in> (Q))))), %m_1. (fapply ((m_1), (''voted'')))))))))), %t. (((''slot'' :> (fapply ((t), (''slot'')))) @@ (''val'' :> (fapply ((t), (''val'')))))))) : ((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((b), (fapply ((d), (''slot''))), (fapply ((d), (''val'')))) :: c)))"(is "PROP ?ob'350")
proof -
ML_command {* writeln "*** TLAPS ENTER 350"; *}
show "PROP ?ob'350"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 350"; *} qed
end
