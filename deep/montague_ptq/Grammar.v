(* PTQ section 1, pp. 18-22. These are typed analysis trees, not strings.
   Surface operations F0-F15 (morphology/pronoun realization) are a separate
   obligation. Each constructor names its source syntactic rule. *)
From Coq Require Import List.
From MontaguePTQ Require Import Syntax.
Set Implicit Arguments.

Inductive iv_word := run | walk | talk | rise | change.
Inductive cn_word := man | woman | park | fish | pen | unicorn | price | temperature.
Inductive tv_word := find | lose | eat | love | date | seek | conceive.
Inductive iav_word := rapidly | slowly | voluntarily | allegedly.
Inductive prep_word := in_ | about.
Inductive attitude_word := believe_that | assert_that.
Inductive control_word := try_to | wish_to.
Inductive proper_name := john | mary | bill | ninety.

(* Domain of the paper's injective lexical map g: the three exceptional
   classes (names/pronouns, be, necessarily) are handled by T1(b-e). *)
Inductive lexeme : cat -> Type :=
| liv : iv_word -> lexeme IV
| lcn : cn_word -> lexeme CN
| ltv : tv_word -> lexeme TV
| liav : iav_word -> lexeme IAV
| lprep : prep_word -> lexeme (slash IAV NP)
| latt : attitude_word -> lexeme (slash IV ct)
| lcontrol : control_word -> lexeme (dslash IV IV).

Definition lexical_code {A} (w : lexeme A) : nat :=
  match w with
  | liv w => match w with run => 0 | walk => 1 | talk => 2 | rise => 3 | change => 4 end
  | lcn w => match w with man => 5 | woman => 6 | park => 7 | fish => 8 | pen => 9
      | unicorn => 10 | price => 11 | temperature => 12 end
  | ltv w => match w with find => 13 | lose => 14 | eat => 15 | love => 16
      | date => 17 | seek => 18 | conceive => 19 end
  | liav w => match w with rapidly => 20 | slowly => 21 | voluntarily => 22 | allegedly => 23 end
  | lprep w => match w with in_ => 24 | about => 25 end
  | latt w => match w with believe_that => 26 | assert_that => 27 end
  | lcontrol w => match w with try_to => 28 | wish_to => 29 end
  end.
Definition name_code (n : proper_name) :=
  match n with john => 0 | mary => 1 | bill => 2 | ninety => 3 end.

Theorem lexical_map_injective A B (u : lexeme A) (v : lexeme B) :
  lexical_code u = lexical_code v -> existT lexeme A u = existT lexeme B v.
Proof.
  destruct u; destruct v;
  repeat match goal with
  | x : iv_word |- _ => destruct x
  | x : cn_word |- _ => destruct x
  | x : tv_word |- _ => destruct x
  | x : iav_word |- _ => destruct x
  | x : prep_word |- _ => destruct x
  | x : attitude_word |- _ => destruct x
  | x : control_word |- _ => destruct x
  end; cbn; intro H; try discriminate; reflexivity.
Qed.

Inductive determiner := every | the | a_or_an.
Inductive junction := conjunction | disjunction.
Inductive tense_sign := negative | future | negative_future | perfect | negative_perfect.

Inductive tree : cat -> Type :=
| s1_word : forall A, lexeme A -> tree A
| s1_name : proper_name -> tree NP
| s1_pronoun : nat -> tree NP
| s1_be : tree TV
| s1_necessarily : tree (slash ct ct)
| s2 : determiner -> tree CN -> tree NP
| s3 : tree CN -> nat -> tree ct -> tree CN
| s4 : tree NP -> tree IV -> tree ct
| s5 : tree TV -> tree NP -> tree IV
| s6 : tree (slash IAV NP) -> tree NP -> tree IAV
| s7 : tree (slash IV ct) -> tree ct -> tree IV
| s8 : tree (dslash IV IV) -> tree IV -> tree IV
| s9 : tree (slash ct ct) -> tree ct -> tree ct
| s10 : tree IAV -> tree IV -> tree IV
| s11 : junction -> tree ct -> tree ct -> tree ct
| s12 : junction -> tree IV -> tree IV -> tree IV
| s13 : tree NP -> tree NP -> tree NP
| s14 : tree NP -> nat -> tree ct -> tree ct
| s15 : tree NP -> nat -> tree CN -> tree CN
| s16 : tree NP -> nat -> tree IV -> tree IV
| s17 : tense_sign -> tree NP -> tree IV -> tree ct.
Arguments s1_word {A} _.

Definition bill_walks := s4 (s1_name bill) (s1_word (liv walk)).
Definition every_man_walks := s4 (s2 every (s1_word (lcn man))) (s1_word (liv walk)).
Definition a_man_walks := s4 (s2 a_or_an (s1_word (lcn man))) (s1_word (liv walk)).
Definition the_man_walks := s4 (s2 the (s1_word (lcn man))) (s1_word (liv walk)).
Definition seeks_unicorn_dicto := s4 (s1_name john)
  (s5 (s1_word (ltv seek)) (s2 a_or_an (s1_word (lcn unicorn)))).
Definition seeks_unicorn_re := s14 (s2 a_or_an (s1_word (lcn unicorn))) 0
  (s4 (s1_name john) (s5 (s1_word (ltv seek)) (s1_pronoun 0))).
