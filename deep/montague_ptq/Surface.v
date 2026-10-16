(* PTQ F0-F15, pp. 19-21. Typed tokens preserve lexical identity while
   word forms change. Non-pronominal F10 requires the specified first
   occurrence; it returns None when that operation has no target. *)
From Coq Require Import List Bool Arith Strings.String Numbers.DecimalString.
From MontaguePTQ Require Import Syntax Grammar Examples.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.

Inductive gender := masculine | feminine | neuter.
Inductive pron_case := subject_case | object_case.
Inductive verb_word := viv (v : iv_word) | vtv (v : tv_word) | vbe
  | vatt (v : attitude_word) | vcontrol (v : control_word).
Inductive verb_form := infinitive | present | neg_present | future_form
  | neg_future_form | perfect_form | neg_perfect_form.
Inductive token := literal (s : string) | noun (c : cn_word) | name (n : proper_name)
  | verb (v : verb_word) (f : verb_form)
  | indexed (n : nat) (c : pron_case) | plain (g : gender) (c : pron_case).

Definition noun_text c := match c with man => "man" | woman => "woman" | park => "park"
  | fish => "fish" | pen => "pen" | unicorn => "unicorn" | price => "price"
  | temperature => "temperature" end.
Definition name_text n := match n with john => "John" | mary => "Mary"
  | bill => "Bill" | ninety => "ninety" end.
Definition noun_gender c := match c with man => masculine | woman => feminine | _ => neuter end.
Definition name_gender n := match n with john | bill => masculine | mary => feminine | ninety => neuter end.
Definition pronoun_text g c := match g,c with
  | masculine,subject_case => "he" | masculine,object_case => "him"
  | feminine,subject_case => "she" | feminine,object_case => "her"
  | neuter,_ => "it" end.
Definition verb_head v := match v with
  | viv w => match w with run => "run" | walk => "walk" | talk => "talk" | rise => "rise" | change => "change" end
  | vtv w => match w with find => "find" | lose => "lose" | eat => "eat" | love => "love"
      | date => "date" | seek => "seek" | conceive => "conceive" end
  | vbe => "be"
  | vatt w => match w with believe_that => "believe" | assert_that => "assert" end
  | vcontrol w => match w with try_to => "try" | wish_to => "wish" end end.
Definition present_head v := match v with
  | vbe => "is" | vcontrol try_to => "tries" | vcontrol wish_to => "wishes"
  | _ => (verb_head v ++ "s")%string end.
Definition perfect_head v := match v with
  | viv run => "run" | viv rise => "risen" | viv walk => "walked" | viv talk => "talked"
  | viv change => "changed" | vtv find => "found" | vtv lose => "lost"
  | vtv eat => "eaten" | vtv love => "loved" | vtv date => "dated"
  | vtv seek => "sought" | vtv conceive => "conceived" | vbe => "been"
  | vatt believe_that => "believed" | vatt assert_that => "asserted"
  | vcontrol try_to => "tried" | vcontrol wish_to => "wished" end.
Definition verb_tail v := match v with vatt _ => ["that"] | vcontrol _ => ["to"] | _ => [] end.
Definition verb_words v f :=
  ((match f with
  | infinitive => [verb_head v] | present => [present_head v]
  | neg_present => match v with vbe => ["is"; "not"] | _ => ["does"; "not"; verb_head v] end
  | future_form => ["will"; verb_head v] | neg_future_form => ["will"; "not"; verb_head v]
  | perfect_form => ["has"; perfect_head v] | neg_perfect_form => ["has"; "not"; perfect_head v]
  end) ++ verb_tail v)%list.

Definition token_words u := match u with
  | literal s => [s] | noun c => [noun_text c] | name n => [name_text n]
  | verb v f => verb_words v f
  | indexed n c => [(pronoun_text masculine c ++ "_" ++ NilZero.string_of_uint (Nat.to_uint n))%string]
  | plain g c => [pronoun_text g c] end.
Definition words (us : list token) := flat_map token_words us.

Definition lex_tokens {A} (w : lexeme A) : list token :=
  match w with
  | liv v => [verb (viv v) infinitive] | ltv v => [verb (vtv v) infinitive]
  | lcn c => [noun c]
  | liav w => [literal (match w with rapidly => "rapidly" | slowly => "slowly"
      | voluntarily => "voluntarily" | allegedly => "allegedly" end)]
  | lprep w => [literal (match w with in_ => "in" | about => "about" end)]
  | latt w => [verb (vatt w) infinitive] | lcontrol w => [verb (vcontrol w) infinitive] end.

Fixpoint first_gender (us : list token) : option gender := match us with
  | [] => None | noun c :: _ => Some (noun_gender c) | name n :: _ => Some (name_gender n)
  | indexed _ _ :: _ => Some masculine | _ :: rest => first_gender rest end.
Fixpoint inflect_first f (us : list token) : option (list token) := match us with
  | [] => None | verb v _ :: rest => Some (verb v f :: rest)
  | u :: rest => match inflect_first f rest with Some out => Some (u :: out) | None => None end end.
Definition replace_pronoun n g u := match u with
  | indexed m c => if Nat.eqb n m then plain g c else u | _ => u end.
Definition rename_pronoun n k u := match u with
  | indexed m c => if Nat.eqb n m then indexed k c else u | _ => u end.
Fixpoint insert_first n (alpha : list token) g (us : list token) : option (list token) :=
  match us with
  | [] => None
  | u :: rest =>
      if match u with indexed m _ => Nat.eqb n m | _ => false end
      then Some (alpha ++ map (replace_pronoun n g) rest)%list
      else match insert_first n alpha g rest with Some out => Some (u :: out) | None => None end
  end.
Definition bare_pronoun alpha := match alpha with
  | [indexed k subject_case] => Some k | _ => None end.
Definition f10 n alpha phi := match bare_pronoun alpha with
  | Some k => Some (map (rename_pronoun n k) phi)
  | None => match first_gender alpha with Some g => insert_first n alpha g phi | None => None end
  end.
Definition object_form beta := match beta with
  | [indexed n subject_case] => [indexed n object_case] | _ => beta end.
Definition combine (f : list token -> list token -> option (list token))
  (a b : option (list token)) := match a,b with Some x,Some y => f x y | _,_ => None end.
Definition concat_tokens (x y : list token) := Some (x ++ y)%list.
Definition join_tokens j x y := Some (x ++ [literal (match j with conjunction => "and" | disjunction => "or" end)] ++ y)%list.
Definition subject_verb f alpha delta :=
  match inflect_first f delta with Some out => Some (alpha ++ out)%list | None => None end.
Definition sign_form k := match k with negative => neg_present | future => future_form
  | negative_future => neg_future_form | perfect => perfect_form | negative_perfect => neg_perfect_form end.

Fixpoint realize {A} (u : tree A) : option (list token) := match u with
  | s1_word w => Some (lex_tokens w) | s1_name n => Some [name n]
  | s1_pronoun n => Some [indexed n subject_case] | s1_be => Some [verb vbe infinitive]
  | s1_necessarily => Some [literal "necessarily"]
  | s2 d c => match realize c with
      | Some cs => Some (literal (match d with every => "every" | the => "the" | a_or_an => "a" end) :: cs)
      | None => None end
  | s3 c n p => combine (fun cs ps => match first_gender cs with
      | Some g => Some (cs ++ [literal "such"; literal "that"] ++ map (replace_pronoun n g) ps)%list
      | None => None end) (realize c) (realize p)
  | s4 p q => combine (subject_verb present) (realize p) (realize q)
  | s5 p q => combine (fun x y => concat_tokens x (object_form y)) (realize p) (realize q)
  | s6 p q => combine (fun x y => concat_tokens x (object_form y)) (realize p) (realize q)
  | s7 p q => combine concat_tokens (realize p) (realize q)
  | s8 p q => combine concat_tokens (realize p) (realize q)
  | s9 p q => combine concat_tokens (realize p) (realize q)
  | s10 p q => combine (fun x y => concat_tokens y x) (realize p) (realize q)
  | s11 j p q => combine (join_tokens j) (realize p) (realize q)
  | s12 j p q => combine (join_tokens j) (realize p) (realize q)
  | s13 p q => combine (join_tokens disjunction) (realize p) (realize q)
  | s14 p n q => combine (f10 n) (realize p) (realize q)
  | s15 p n q => combine (f10 n) (realize p) (realize q)
  | s16 p n q => combine (f10 n) (realize p) (realize q)
  | s17 k p q => combine (subject_verb (sign_form k)) (realize p) (realize q)
  end.
Definition surface {A} (u : tree A) := option_map words (realize u).

Example bill_walks_surface : surface bill_walks = Some ["Bill";"walks"].
Proof. reflexivity. Qed.
Example unicorn_surface_ambiguity :
  surface seeks_unicorn_dicto = Some ["John";"seeks";"a";"unicorn"] /\
  surface seeks_unicorn_re = surface seeks_unicorn_dicto.
Proof. split; reflexivity. Qed.
Example temperature_surface : surface temperature_is_ninety = Some ["the";"temperature";"is";"ninety"].
Proof. reflexivity. Qed.
Example tense_surface : surface (s17 negative_perfect (s1_name john) (s5 (s1_word (ltv eat)) (s1_name mary))) =
  Some ["John";"has";"not";"eaten";"Mary"].
Proof. reflexivity. Qed.
Example missing_first_occurrence_is_reported :
  surface (s14 (s2 a_or_an (s1_word (lcn unicorn))) 9 bill_walks) = None.
Proof. reflexivity. Qed.
Example first_and_later_occurrences_differ :
  option_map words (f10 0 [name mary]
    [indexed 0 subject_case; verb (vtv love) present; indexed 0 object_case]) =
  Some ["Mary";"loves";"her"].
Proof. reflexivity. Qed.
