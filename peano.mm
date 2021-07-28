$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Metamath source file: axioms for Peano arithmetic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( Copyright (GPL) 2004 Robert Solovay, PO Box 5949, Eugene OR, 97405   $)
$( Comments welcome; email to:  solovay at gmail dot com $)

$( Version of 22-Jun-2021 $)
$( Replaces prior version of 13-July-04 $)
$( 22-Jun-2021 (Patrick Brosnan) - Add missing distinct variable constraints
   to pa_ax7 $)
$( 7-Oct-2004 (N. Megill) - Minor fixes to conform to strict Metamath spec $)
$( 11-Oct-2004 (N. Megill) - "$a implies" --> "$a |- implies" at line 224 $)
$( 24-Jun-2006 (N. Megill) - Made label and math symbol names spaces
       disjoint, as required by the 24-Jun-2006 modification of the Metamath
       specification.  Specifically, the labels binop, logbinop, binpred,
       and quant were changed to binop_, logbinop_, binpred_, and quant_
       respectively. $)
$( 11-Nov-2014 (N. Megill) - updated R. Solovay's email address $)

$( This file is a mixture of two sorts of things:

1) Formal metamath axioms and supporting material. [$f and $d
   statements for example.]

2) Informal metamathematical arguments that show our axioms suffice to
   "do Peano in metamath".

All our metamathematical arguments are quite constructive and
certainly could be formalized in Primitive Recursive Arithmetic. $)

$( We shall slightly deviate from the treatment in Appendix C of the
metamath book. We assume that for each constant c an infinite subset
of the variables is preassigned to that constant.

In particular we will have a constant var. Among our other constants
will be all the symbols of Peano arithmetic except the variables. The
variables of the formal language of Peano Arithmetic will be
identified with the variables attached to the constant symbol var. In
this way each well formed formula or term of PA will *be* a certan
metamath expression. $)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
            Syntax
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$c |-  wff term var $.

$( The next set of axioms will give the inductive definition of
terms. We will be using Polish notation in our formal development of
the syntax of PA. $)

$v s t u s0 s1 t0 t1 $.

ts $f term s $.
tt $f term t $.
tu $f term u $.
ts0 $f term s0 $.
ts1 $f term s1 $.
tt0 $f term t0 $.
tt1 $f term t1 $.

$v v x y z $.
varv $f var v $.
varx $f var x $.
vary $f var y $.
varz $f var z $.

$c 0 S + * $.

$( It is often possible to treat + and * in parallel. The following
device allows us to do this. $)

$c BINOP $.
$v binop $.
binop_ $f BINOP binop $.
binop_plus $a BINOP + $.
binop_times $a BINOP * $.

tvar $a term v $.
tzero $a term 0 $.
tsucc $a term S s $.
tbinop $a term binop s t $.

$( The next set of axioms will give the inductive definition of wff $)

$c not or and implies iff $.
$c LOGBINOP $.
$v logbinop $.
logbinop_ $f LOGBINOP logbinop $.
logbinopor $a LOGBINOP or $.
logbinopand $a LOGBINOP and $.
logbinopimplies $a LOGBINOP implies $.
logbinopiff $a LOGBINOP iff $.

$c = < $.
$c BINPRED $.
$v binpred $.
binpred_ $f BINPRED binpred $.
binpred_equals $a BINPRED = $.
binpred_less_than $a BINPRED < $.

$c forall exists $.
$c QUANT $.
$v quant $.
quant_ $f QUANT quant $.
quant_all $a QUANT forall $.
quant_ex $a QUANT exists $.

$v phi psi chi $.
wff_phi $f wff phi $.
wff_psi $f wff psi $.
wff-chi $f wff chi $.

wff_atom $a wff binpred s t $.
wff_not $a wff not psi $.
wff_logbinop $a wff logbinop psi phi $.
wff_quant $a wff quant v phi $.

$( This completes our description of the syntactic categories of wff
and term $)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
            "Correct" axioms
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( In the various sections of this file we will be adding various
axioms [$a statements]. The crucial correctness property that they
will have is the following:

     Consider a substitution instance of the axiom such that the only
     variables remaining in the instance [in either hypothesis or
     conclusion] are of type var. Then if all the hypotheses [$e
     statements] have the form
          |- phi
     [where phi is a theorem of PA] then the conclusion is also a
     theorem of PA.

     The verification that the various axioms we add are correct in
     this sense will be "left to the reader". Usually the proof that I
     have in mind is a semantic one based upon the consideration of
     models of PA. $)
$( I will give a discussion at the end of this document as to why
     sticking with this correctness condition on axioms suffices to
     guarantee that only correct theorems of Peano arithmetic are
     proved.
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
         Propositional logic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( We follow closely the treatment in set.mm. We do have to change the
axioms "into Polish". $)

ax-1 $a |- implies phi implies psi phi $.

ax-2 $a |- implies
              implies phi implies psi chi
              implies
                 implies phi psi
                 implies phi chi  $.
ax-3 $a |- implies
              implies not phi not psi
              implies psi phi $.

$( Modus ponens: $)
${
   min $e |- phi $.
   maj $e |- implies phi psi $.
   ax-mp $a |- psi $.
$}

bi1 $a |- implies
          iff phi psi
          implies phi psi $.
bi2 $a |- implies
          iff phi psi
          implies psi phi $.
bi3 $a |- implies
          implies phi psi
          implies
             implies psi phi
             iff phi psi $.
df-an $a |- iff
               and phi psi
               not implies phi not psi $.
df-or $a |- iff
               or phi psi
               implies not phi psi $.

$( Equality axioms $)

$( From here on out, I won't make an effort to cordinate labels
between my axioms and those of set.mm $)

eq-refl $a |- = t t $.
eq-sym $a |- implies = s t = t s $.
eq-trans $a |- implies
                and = s t = t u
                = s u $.
eq-congr $a |- implies
            and = s0 s1 = t0 t1
            iff binpred s0 t0 binpred s1 t1 $.

$( The next two axioms were missing in the previous draft of
peano.mm. They are definitely needed. $)

eq-suc $a |- implies
                  = s t
                  = S s S t $.
eq-binop $a |- implies
                  and = s0 s1 = t0 t1
                  = binop s0 t0 binop s1 t1 $.

$( Lemma 1 $)

$( Lemma 1 of the 2004 version of this document was not needed in the
subsequent development and has been deleted. I decided not to change
the numbering of subsequent lemmas. $)


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
             Free and bound variables; alpha equivalence
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( It will be useful to warm up with some familiar concepts. Let PHI
   be a well-formed formula of Peano arithmetic. Then Phi is a finite
   sequence of symbols, s_1 ... s_n.

   Following Shoenfield's treatment in "Mathematical Logic" we use the
   term "designator" for a sequence of symbols that is either a term
   or a wff. A basic result says that each s_i is the initial symbol
   of precisely one subsequence of s_1 ... s_n which is a designator.

   Suppose that s_i is a variable. We say that s_i is bound in PHI if
   there is a subformula of PHI containing s_i whose initial symbol is
   a quantifier and whose second symbol is the same variable as s_i.

   [Otherwise s_i is *free* in PHI.]

   If s_i is a bound variable, then there is a shortest subformula of
   PHI in which s_i is bound. The quantifier beginning this subformula
   is the quantifier that *binds* s_i. $)

$( alpha equivalence $)

$( Let Phi_1 and Phi_2 be well-formed formulas of PA. Say Phi_1 is s_1
... s_n and Phi_2 is t_1 ... t_m.

    We say that Phi_1 and Phi_2 are alpha-equialent if:

1) n = m.

2) Let 1 <= i <= n. Then s_i is a constant iff t_i is; in that case,
   they are the *same* constant.

3) Let 1 <= i <= n. Suppose that s_i is a variable. [So t_i is a
   variable as well.] Then s_i is free in Phi_1 iff t_i is free in
   Phi_2. If s_i is free in Phi_1, then s_i = t_i.

4) Let 1 <= i <= n. Suppose that s_i is a variable that is bound in
   Phi_1. [It follows that t_i is a variable that is bound in Phi_2.]
   Let s_j be the quantifier that binds s_i. Then t_j is the
   quantifier that binds t_i.

[This ends the definition of alpha-equivalence.]

It is indeed true that alpha-equivalence is an equivalence relation.
$)

$( Trim formulas $)

$( The following concept is non-standard. A well-formed formula of PA
is *trim* if:

   1) No variable occurs both free and bound in Phi.

   2) Distinct quantifiers bind distinct variables.

[So
exists x exists x = x x
is not trim since the two quantifiers both bind the variable x.]

   Clearly every formula is alpha-equivalent to some trim
   formula. Moreover, we can assume that the bound variables of this
   trim equivalent avoid some specified finite set of variables.
$)

$( Here is the next Lemma we are heading toward. We can add a finite
number of correct axioms to our file so that once this is done, if
Phi_1 and Phi_2 are alpha-equivalent formulas then [subject to the
requirement that any pair of distinct  variables appearing in Phi_1 or
Phi_2 is declared disjoint]

      |- iff Phi_1 Phi_2
is a theorem of Metmath [i.e. follows from the given axioms].

In view of the remarks about trim formulas, we are reduced to the
following special case: Phi_2 is trim and no bound variable of Phi_2
appears [free or bound] in Phi_1.

We fix Phi_1 and Phi_2 subject to this restriction. We will develop
the axioms we need in the course of the proof. Of course, the reader
should verify that we could have specified them in advance. In
particular the additional axioms we list will not depend on Phi_1 or Phi_2. $)

$( Our proof strategy is as follows;

To each subformula Psi of Phi_1, we shall attach a claim C(Psi) [which
will also be a well-formed formula of PA]. We will prove in Metamath
the various claims C(Psi). The construction of these proofs will be an
inductive one [by induction on the length of the subformula,
say]. From the claim C(Phi_1), the desired equivalence of Phi_1 and
Phi_2 will easily follow. $)

$( Weak alpha-equivalence $)

$( Before describing the claims C(Psi), I need to introduce the notion
of weak alpha-equivalence. Let Psi_1 and Psi_2 be two well-formed
formulas of PA.

Say Psi_1 is s_1 ... s_m and Psi_2 is t_1 ... t_n.

Then Psi_1 and Psi_2 are weakly alpha equivalent iff:

1) m = n;

2) Let 1 <= i <= n. Then s_i is a constant iff t_i is; in that case,
   they are the *same* constant.

3) Let 1 <= i <= n. Suppose that s_i is a variable. [So t_i is a
   variable as well.] Then s_i is free in Psi_1 iff t_i is free in
   Psi_2.

3a) Let 1 <= i < j <= n. Suppose that s_i and s_j are variables free
in Psi_1. [It follows that t_i and t_j are free variables in Psi_2.]
Then s_i = s_j iff t_i = t_j.

4) Let 1 <= i <= n. Suppose that s_i is a variable that is bound in
   Psi_1. [It follows that t_i is a variable that is bound in Psi_2.]
   Let s_j be the quantifier that binds s_i. Then t_j is the
   quantifier that binds t_i.

[This ends the definition of weak alpha-equivalence.] $)

$( I need a pedantic fact:

   Proposition 2.1. Let Phi_1 = s_1,..., s_m and Phi_2 = t_1...t_m be
   as above. Let 1 <= i <= j <= m. Then s_i ... s_j is a term
   [formula] iff t_i ... t_j is.

   The proof is by induction on j - i and is straightforward. [It
   splits into cases according to what s_i is.] $)

$( The following explains the importance of "weak alpha equivalence":

   Proposition 2.2.
   Let Psi_1 be a subformula of Phi_1, and Psi_2 the corresponding
   subformula of Phi_2. (Cf. the "pedantic fact" just above.) Then
   Psi_1 and Psi_2 are weakly alpha equivalent.

   Only clause 3a) of the definition of weak alpha equivalence
   requires discussion:

   Say Psi_1 occupies positions i ... j of Phi_1. Let i <= a < b <= j
   and let s_a and s_b be the same variable x. We suppose that s_a and
   s_b are free in Psi_1. We shall show that t_a = t_b. {This will
   prove one direction of the iff; the other direction is proved
   similarly.}

   If s_a and s_b are both free in Phi_1 then our claim is clear since
   Phi_1 and Phi_2 are alpha equivalent. If not, let Theta_1 be the
   smallest subformula of Phi_1 in which one of s_a and s_b is
   bound. Then both s_a and s_b are bound by the quantifer that begins
   Theta_1.

   Let Theta_2 be the subformula of Phi_2 that corresponds to
   Theta_1. Using the alpha equivalence of Phi_1 and Phi_2 we see that
   both t_a and t_b are bound by the quantifer that begins
   Theta_2. Hence t_a = t_b.

   $)

   $( We are now able to begin the definition of C(Psi_1) for Psi_1 a
   subformula of Phi_1. It will have the form

   implies H(Psi_1)
           iff Psi_1 Psi_2

   where Psi_2 is the subformula of Phi_2 that corresponds to Psi_1.

  It remains to describe H(Psi_1):

  Let w be a variable that does not appear [free or bound] in either
  Phi_1 or Phi_2. Let x_1 ... x_r be the free variables appearing in
  Psi_1 [listed without repetitions]. Because Psi_1  is weakly alpha
  equivalent to Psi_2, we can define a bijection between the free
  variables of Psi_1 and those of Psi_2 thus. If x_i appears freely in
  position j of Psi_1 then the corresponding free variable of Psi_2,
  say y_i, appears in position j of Psi_2.

  H(Psi_1) is the conjunction of the following equalities:

  1) = w w ;

  2) = x_i y_i (for i = 1 ... r).

  This completes our description of C(Psi_1). $)

  $( Consider first C(Phi_1). Because Phi_1 is alpha equivalent to
  Phi_2, H(Phi_1) is the conjunction of equalities of the form = a a .
  Hence Metamath can prove H(Phi_1) and can see that C(Phi_1) is
  equivalent to the equivalence:

      iff Phi_1 Phi_2
  $)

$( So it will be sufficient to see that Metamath [after enrichment with
some additional correct axioms] can prove C(Psi_1) for every
subformula Psi_1 of Phi_1. The proof of this proceeds by induction on
the length of Psi_1.

If Psi_1 is atomic, our claim is easily proved using the equality
axioms.

The cases when Psi_1 is built up from smaller formulas using propositional
connectives are easily handled since Metamath knows propositional
logic.

$)

$( It remains to consider the case when Psi_1 has the form Q x Chi_1
where Q is a quantifier.

It is clear that Psi_2 has the form Q y Chi_2 [where Chi_2 is the
subformula of Phi_2 that corresponds to Chi_1]. We will consider two
cases;

Case A: x = y;

Case B: x != y. $)

$( To handle Case A we adjoin the following axiom [which the reader
should verify is correct]. $)

${ $d phi x $.
   alpha_hyp1 $e |- implies phi
              iff psi chi $.
   alpha_1 $a |- implies phi
              iff quant x psi
                  quant x chi $. $}

$( We apply this axiom with H(Psi_1) in the role of phi and Q in the
role of quant. Chi_1 is in the role of psi and Chi_2 is in the role of
chi.

To see that the needed instance of alpha_hyp1 holds, note that
H(Chi_1) is either H(Psi_1) [up to a possible rearrangement of
conjuncts] or the conjunction of H(Psi_1) with the conjunct
= x x

So our needed instance follows from C(Chi_1), equality axioms and
propositional logic $)

$( We turn to case B. It is worthwhile to remind the reader that Phi_2
has been chosen so that no bound variable of Phi_2 appears either free
or bound in Phi_1.

Proposition 2.3. y does not appear [free or bound] in Psi_1. x does
not appear [free or bound] in Psi_2.

Proof: y appears bound in Psi_2. Hence it doesn't even appear [free or
bound] in Phi_1.

Suppose that x appears in Psi_2. Then this appearence must be free in
Phi_2. {Otherwise, x would not appear in Phi_1 but it is the second
symbol of Psi_1.} So at the same spot in Psi_1 x also appears, and
this occurrence is free in Phi_1. {This follows from the fact that
Phi_1 and Phi_2 are alpha equivalent.} But clearly this occurrence of
x in Psi_1 will be bound by the quantifier that starts
Psi_1. Contradiction! $)

$( Proposition 2.3 has the following immediate consequence:

Proposition 2.4: Neither of the variables x or y occurs in H(Psi_1).

	    Also it is easy to check that [up to propositional logic]
	    H(Chi_1) is either H(Psi_1) or the conjunction of H(Psi_1)
	    with
                    = x y

It follows that from C(Chi_1) one can deduce [using propositonal
logic] the following:

(A) implies H(Psi_1)
            implies = x y
            iff Chi_1 Chi_2 $)

$( Next we introduce the following Metamath axiom [which the reader
should verify is correct] $)

${ $d phi x $.

   alpha_hyp2 $e |- implies phi chi $.
   alpha_2    $a |- implies phi forall x chi $.
$}

$( Using this axiom we can deduce from (A) and Proposition 2.4
the following:

(B) implies H(Psi_1)
            forall x forall y implies = x y
                                      iff Chi_1 Chi_2
$)

$( We need to introduce another axiom [which the reader should verify
is correct] $)

${ $d phi y $.
   $d psi x $.
   $d x y $.
   alpha_3 $a |- implies forall x forall y implies = x y
                                   iff phi psi
                         iff quant x phi quant y psi $.
$}

$( From this axiom, (B) and Proposition 2.3 we easily deduce:

(C) implies H(Psi_1)
            iff Psi_1 Psi_2

which is C(Psi_1) $)

$( The following lemma should now be clear to the reader:

Lemma 2. Let Phi and Phi* be alpha equivalent formulas of PA. Then
using the axioms so far introduced, we can prove in Metamath the
sequence

|- iff Phi_1 Phi_2

from the disjointness assumption that all the distinct variables
appearing in Phi_1 or Phi_2 are asserted to be distinct in a $d
assumption.  $)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                Axioms and inference rules of predicate logic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( Our next task is to prove the rule of inference and the axiom
associated to the "forall" quantifier. $)

$( Let's start with the rule of inference. We have to show that if

|- implies phi chi

and phi does not contain x free then also

|- implies phi forall x chi.

   But this is easy. In view of what we have just shown, it is ok to
   replace phi by an alpha-equivalent formula that does not contain x
   at all. {In both our hypothesis and conclusion.}

   But then we just need to invoke the axiom alpha_2. $)

$( We now turn to the axiom of "forall elimination". To state it we
introduce the familiar notion of substituting a term for the free
occurrences of a variable. So let phi be a formula, x a variable and t
a term. By phi[t/x] we mean the formula obtained by simultaneously
replacing each free occurrence of x in phi by a copy of the term t. {A
more rigorous definition would proceed by induction on the structure
of phi.}

   We say that t is substitutable for x at the free occurrence of x in
   phi [or just "substitutable" if we are being terse] if no variable
   occuring in t falls under the scope of any quantifer of
   phi. {Again, I am presuming this notion known; otherwise, I'd be
   more careful with this definition.}

   The final group of axioms of predicate calculus that we need to
   derive have the following form:

(*)   implies
        forall x phi
        phi[t/x]

   **where** t is substitutable for x in phi.

Our next step is to show that it suffices to prove the following
special case of this axiom. phi x and t satisfy the following three
conditions:


	(1) The variable x does not appear in the term t.

        (2) No bound variable of phi appears in t.

        (3) The variable x does not appear bound in phi.

We can see this as follows. We can clearly find a formula
   forall y psi
which is alpha equivalent to forall x phi such that:
     (1') The variable y does not appear in the term t;
     (2') No bound variable of psi appears in t;
     (3') The variable y does not appear bound in psi.

Using the fact that t is substitutable for x in phi we easily see that
phi[t/x] is alpha equivalent to psi[t/y]. It follows that (*) is
alpha-equivalent to:
(**)  implies
        forall y psi
        psi[t/y]

Hence Metamath can prove the equivalence of (*) and (**). But in view
of (1') through (3'), the instance (**) of for all elimination meets
our additional requirements (1) through (3).

In the remainder of our discussion we shall assume then that phi, x
and t meet the requirements (1) through (3). Note that it follows from
(2) that t is substitutable for x in phi.

[N.B. We cannot assume that the variables appearing in t do not appear
in phi.]

Here is the key idea of our approach: The formula phi[t/x] (under the
hypotheses (1) -- (3) just given) is equivalent to:

forall x implies
            = x t
            phi

$)

$( We start by adding the following [correct!] axiom $)

${ $d x t $.
   all_elim $a |- implies
                   forall x phi
                   forall x implies
                              = x t
                              phi $.
$}

$( Using this axiom we can reduce our proof that Metamath proves all
instances of "all elimination" to the following lemma:

Lemma 3. Let t be a term of PA and phi a formula of PA. We assume:
1) The variable x does not occur in t;
2) No bound variable of phi appears in t.
3) The variable x does not occur bound in phi.

Then [after adding finitely many additional correct axioms whose
choice does not depend on phi] we can prove in Metamath:

|- iff
     forall x implies
        = x t
        phi
    phi[t/x]

$)

$( We shall need a preliminary result:

Proposition 3.1 Let phi t and x obey our standing hypotheses 1) --
3). Let psi be a subformula of phi.

Then [after adding finitely many additional correct axioms whose
choice does not depend on phi] we can prove in Metamath:

|- implies = x t
           iff psi psi[t/x]

The construction of such proofs [like many previous arguments] is by
induction on the tree of subformulas of phi. $)

$( The first case is when psi is atomic. This case is easily handled
using the equality axioms.

The second case is when the principal connective of psi is a
propositional connective. This case follows easily using propositional
logic from our inductive hypotheses concerning the subformulas of psi.

$)

$( The final case is when the principal connective of psi is a
quantifier. This case is handled using the following axiom: $)

${ $d x y $.
   $d y t $.
   all_elim_hyp2 $e |- implies = x t
                    iff phi chi $.
   all_elim2 $a |- implies = x t
                   iff quant y phi
                       quant y chi $.
$}

$( The proof of Proposition 3.1 is now complete. We apply it to phi
and get that Metamath proves:
|- implies = x t
           iff phi phi[t/x]

Here phi and t stand for the particular wff and term of t under
discussion and are not literal metavariables of Metamath.

We also know at this point that Metamath proves:

|- implies forall x phi
           forall x implies = x t
                    phi

We would be done if we could prove in Metamath:

|- implies forall x implies = x t
                            phi
           phi[t/x]

But this will follow easily from the next axiom [which is inelegant
but correct].

 $)

${
$d x chi $.
$d x t $.

 all_elim3_hyp1 $e |- implies = x t
                           iff phi chi $.
all_elim3 $a |- implies forall x implies = x t
                                         phi
                     chi $. $}

$( This completes our discussion of "forall-elimination". $)
$( It is time to introduce the definition of the
"exists" quantifier $)

exists_def $a |- iff
              exists x phi
              not forall x not phi $.

$( Of course, the axiom and rule of inference for "exists" follow from
this definition and the corresponding inference rule or axiom scheme
for "forall". $)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
         The non-logical axioms of Peano Arithmetic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( At this point, we know that Metamath can prove any logically valid
wff of PA. It remains to add the axioms of PA. $)

$( First we give the particular axioms of PA. Then we discuss the
induction scheme $)

pa_ax1 $a |- not = 0 S x $.
pa_ax2 $a |- implies = S x S y
                     = x y $.
pa_ax3 $a |- = x
               + x 0 $.
pa_ax4 $a |- = S + x y
               + x S y $.
pa_ax5 $a |- = 0
               * x 0 $.
pa_ax6 $a |- = + * x y x
               * x S y $.
${
  $d z x $.  $d z y $.
  pa_ax7 $a |- iff
               < x y
               exists z = y + x S z $.
$}

$( It suffices to give the induction axiom for the case when phi does
not contain x free. For the usual form of the axiom follows from this
special case by first order logic. $)

${
$d phi x $.
$d x y $.
induction $a
|- implies
   and forall y implies = y 0 phi
       forall x implies forall y implies = y x phi
                        forall y implies = y S x phi
   forall x forall y implies = y x phi $.
$}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
           Discussion of correctness
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
Let's agree that when I say "Metamath proves PHI" I mean "Metamath"
enriched with all the preceding axioms in this document.

The issue is the following. For what formulas Phi is there a proof in
Metamath from no $e type assumptions of the sequencce
    |- Phi.

(Recall that I am identifying the well-formed formulas of Peano with
certain of the Metamath strings of symbols. This is done by
identifying the object variables of our language with the
metavariables of type var.)

The claim is that these are precisely those Phi which are theorems of
the usual formulation of Peano Arithmetic.

One direction should be clear by this point. We have developed the
first order predicate calculus within Metamath and included the usual
axioms of Peano arithmetic [or equivalents]. So any theorem of Peano
Arithmetic [as usually formulated] can be proved in Metamath.

To go in the other direction, suppose that there is a proof in
Metamath of |- Phi. So the final line of the proof contains only
variables of type var. But there might well be variables of other
kinds in the body of the proof. For example, there might be a variable
phi of kind wff.

The critical such variables are those that appear in lines of the
proof beginning with |-.  What we do is replace such variables (of
kind different than var) [one by one] by sequences of constants of the
same type.  (So phi might be replaced by the three symbol string "= 0
0".) It is not hard to see that after this substitution the result can
be massaged to a correct proof. There are two points to notice.

     a) Since the string by which we replaced the variable contains no
     variables itself the process converges and no disjointness
     conditions [$d restrictions] are violated.

     b) We may have to add a trivial few lines to prove the "type
     assertion". In our example, the line "wff phi" will be replaced
     by the line "wff = 0 0". This line is no longer immediate but
     must be proved by a four line argument.

At the end, there results a proof where all the lines that begin with
"|-" contain only variables of type var. But now our correctness
assumptions allow us to verify step by step that each such line is a
theorem of Peano arithmetic.
$)

$( For Emacs $)
$( Local Variables: $)
$( eval:'(show-paren-mode t) $)
$( End: $)
$(

###############################################################################

                Metamath version of Lean's Natural Numbers Game

                                                  Contributed by Patrick Brosnan


                                        Es gibt nichts Gutes, ausser man tut es.
                                                              
                                                              --- Erich Kaestner

#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                                  Introduction
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

What follows is a development of Peano arithmetic using the axioms from the
file peano.mm included in the metamath distribution as a starting point.

My original (exceedingly naive) goal in starting this project was to emulate
the Lean Natural Numbers Game tutorial written by Kevin Buzzard and Mohammad
Pedramfar.  It very quickly became apparent that lean and metamath are
extremely different programs.  Metamath the program "knows" essentially nothing
about mathematics.  You have to teach it everything.  The benefit of this
approach is that, after a very short time working with it, it becomes pretty
clear how metamath works.  Lean on the other hand comes with enough "tactics"
for proving theorems that the user gets the sense that it knows some
mathematics. However, what is going on inside of the lean program seems hidden
(at least to me).

One consequence of this is that it takes a LOT longer to start writing proofs
of theorems about natural numbers in metamath than it does in lean. 
Moreover, while a mathematician or a math student can use lean without 
knowing much about its logical underpinnings (type theory), it seems
very difficult to do this with metamath.  To use metamath effectively,
you are basically forced to learn a little about basic mathematical
logic.

So, while the goal of this development of Peano Arithmetic is really to help 
people to use metamath by starting out with something simple, it took me 
much longer to work through than the Lean Natural Numbers Game, and the same
will almost certainly hold for anyone else who works through it.  On the other
hand, for me, setting up basic Peano Arithmetic in metamath using Solovay's 
file was enormously educational and also a lot of fun.  My hope is that 
it will be the same for other people working with this file.

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Advice for using this file for learning metamath 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

It seems like the easiest way to get started learning from this file
would be to reprove some of the theorems.   For this, you need the metamath
program and the Metamath Book to learn the basics of interacting
with the proof assistant.  Section 2.4, titled of the Metamath Book has a 
walk-through of the Proof Assistant titled "Your First Proof." 
The first step is to enter the Proof Assistant on a theorem and 
then type "delete all" to delete the proof.  After this  
you can replace the proof given here with your own proof.
For example, you can start with the first theorem, ax2d, given
in this file.

You can also browse the proofs given in this file using the
metamath command "show proof." And below in the subsection
on the Proof Assistant I give some thoughts about using it,
which I hope will be helpful.

Aside from the Metamath Book, "Introduction to Mathematical Logic,"
by Elliott Mendelson was incredibly helpful to me in coming up with 
the proofs, especially in the early stages of the development.
Towards the end, I also used Shoenfield's book "Mathematical Logic,"
which is reference by Solovay in the text above.  Solovay's handling
of quantifiers seems a little bit more similar to Shoenfield's than
to Mendelson's.   

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                                Polish notation
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

One of the downsides of peano.mm, which is really clear from the start,
is the Polish notation.  I managed to work with it for quite a long time,
but the problem is always that it is hard to tell when one subexpression
ends and another begins.  I wanted to stick with it at first partially 
because I thought it would be a good way to internalize the reverse Polish
notation used by the metamath proof stack.  And maybe it did help somewhat 
with that.  However, when coupled with the bare bones nature of the metamath
proof assistant, the Polish notation sometimes becomes a big problem.

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                            Metamath Proof Assistant 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

The "bare bones nature" of the metamath proof assistant has some serious
upsides as well.  When you start out, there are really only two "tactics" to
learn

1) assign; 
2) let.

The first one assigns a step to an axiom or previously proved theorem,
and the second assigns a variable to an arbitrary expression that you 
get to write down.  In order to finish a proof and get it to compile
there are a few more things you should know, which are documented very
well in the Metamath Book.  The main ones are 

3) improve;
4) save new_proof;
5) verify;  
6) write source.

Improve (usually) fills in any details in the proof which were left hanging in
the proof assistant.  The point here is that, in metamath, the parsing job of
showing that a wff really is a wff or, in peano.mm, that a term really is a
term is in some sense logically part of the proof.  But it is cleverly hidden
for the most part and left for the machine to do.  Most of the time the machine
can.  But sometimes it struggles and you have to increase the memory.  (See the
case of the theorem "addcanc_ind" below for this.) And sometimes you even have
to help it out yourself manually, as was the case for me in the proof of the
induction theorem "indi" below.  (Unfortunately, I don't have any advice about
how to help it out manually, and I don't think I would be able to reproduce
what I did for indi.)

"Save new_proof" is important just because you shouldn't forget to do it or
your proof will be lost.  I always write "save new / com" (using abbreviations)
to save the proof in compressed form.  Otherwise you wind up with a long file.

"Verify" is important because the proof assistant doesn't check everything.
One major thing it doesn't check is disjoint variable assumptions.  But, like
the Metamath Book says, verify points out where these are missing, and you can
fix them after the fact in the file, read it back in,  and then use verify
again to make sure you did it correctly.  But also "improve" doesn't always
work.  So you really seem to need that verify step to be sure even if you're
not worried about disjoint variables.

The one thing I found myself wanting in the metamath proof assistant is just a
tiny bit more flexibility with unifying. What happens when you assign a step is
that the unifier presents you with various options on how to assign variables.
When I had several variables to assign it was often the case that, for example,
variable $3 would be correct but $4 was wrong. (Metamath knows no math. So the
suggestions it gives are nonsensical most of the time.) I was wishing that I
could keep the correct suggestion for $3 and then move on to deal with $4 and
the other variables.  When I had a lot of variables to assign, I would either
(a) quit the unifier and assign things myself or (b) sit there hitting "r" (for
reject) and return repeatedly until the right assignment came up.  Option (b)
was annoying but safer because, if make a mistake in the variable assignment by
copying something in wrong, it can basically trash the proof. 

I've heard that mmj2, the java program by Mel O'Cat with another metamath proof
assistant, has a better unifier.  But I never got it to work on my main machine
(a MacBook Air).  Part of this was my incompetence at installing Java.  It took
me a while to get both java and a javascript plugin working (maybe because I
used OpenJDK 16).  Then, when I finally got it working, mmj2 gave me an error
about "binop" when reading this file.  (I'm not sure what it doesn't like about
the appearance of "binop" here.) 

When I first started with the metamath proof assistant, I was confused by the
notion of the proof stack.  (As I said above, that was one of the reasons I
decided to stick with Polish notation.)  I would try to write the proofs out
meticulously thinking a lot about the order of the statements.  After a while,
this became a lot more automatic.  Still, while I would "wing it" on the
smaller proofs, for anything serious I would write down the proofs beforehand
more or less in the form that they appear when you type 
  
    show proof thm /lem /ren

The one difference is that I would follow the advice I've seen from the mmj2
people and multiply the numbers by 10 so that I could fit new statments in if I
forgot.  This all went in a file called scratch.txt.  For example, here is an
expert from scratch.txt of my proof of the theorem "contrad." (The theorem says
that, if the hypotheses contrad.1 and contrad.2 hold, so that phi implies both
psi and not psi, then phi implies chi, where chi is any wff.) 

  contrad
  10 h2 implies phi not psi
  20 h1 implies phi psi
  30 andant 10, 20 implies phi and not psi psi
  40 contra implies not psi implies psi chi
  50 simpandr 40 implies and not psi psi chi
  60 syl 30 50 implies phi chi

Here h1 and h2 are just shorthand I learned from the mmj2 documentation
for the first and second hypothesis, in this case contrad.1 and 
contrad.2.   

One benefit of writing things out beforehand is that, while the proof assistant
supports proving theorems only in the backward direction, when you write it out
you get to think of it mostly in the forward direction.  I say "mostly" because
you do have to worry about what happens in the proof stack.  For example,
notice that every line number on the left in the above example except the last
one also appears somewhere on the right. This has to happen because, part of
the metamath specification is that there be only one thing left on the proof
stack when the proof is done.  When I first started working with metamath, this
requirement seemed very difficult to fulfill. But it is actually trivial.
(Just delete unused parts of your proof.)  It is very slightly annoying to
reorder your proof so that the right things go on the stack at the right time.
(Apparently, mmj2 can automate this.)  But I got used to it pretty quickly. 

-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
                                  Minor remark
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

Technically the proof stack contains both the parsing statements
(showing that something is a wff) and the logical proof statements.  But one of
the very nice things about the design of metamath is that you can basically
ignore the parsing statements for visualizing the proof stack.  This is 
really because, although the logical proof statements can (and definitely do)
require parsing statements as antecedents, the other way around never happens.

(Commentary contributed by Patrick Brosnan, 23-Jun-2021.)


#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                              PROPOSITIONAL LOGIC 
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

The first part of this "number theory game" consists of several things about
logic, many of which were shamelessly copied, along with the title above, from
set.mm.  These are theorems I took almost completely for granted despite the
fact that, as a mathematician, I had been using them for most of my life.  It
was something like having to learn to speak English again from the grammar.  

For example, like I think most mathematicians, I had never heard of the
deduction theorem.  I quickly found out what it was when I started learning
metamath (because metamath is basically impossible to use without being aware
of the deduction theorem).   I also learned the words for how the metamath
community gets around the need for a program to turn inferences into
theorems automatically using ideas related to the proof or the deduction
theorem.  In particular, I learned what the deduction form and inference form
of a theorem are.  (See the metamath explorer.) However, when I first started
naming theorems I was still a little bit shaky on these concepts. So, in the
first several weeks of working with peano, I broke the metamath convention that
deduction forms end in the letter "d" and inferences end in the letter "i."
Part of the problem is that I didn't really completely understand how useful
the deduction form is.

When I stole a theorem from set.mm, I usually stole the name along with the
theorem.  However, since the point of this exercise for me was to learn
as much of metamath as I could on my own, many of the theorems here 
duplicate set.mm but with different (and almost always much, much worse) names.

In addition to consulting set.mm, I also occasionally took a peek at Mario
Carneiro's peano.mm0.  This is a development of Peano Arithmetic in Carneiro's
mm0 (with proofs in the file peano.mm1), which starts from a different set of
axioms.  For example, peano.mm0 is not written in Polish notation and I believe
it also has finite sets.  MM1 also has tactics for writing proofs.  For
example, the main induction theorem I use, nindd, which was essentially copied
from set.mm, requires the user to prove several substitution goals.   These
goals are annoying to prove because they are essentially obvious, but the
proofs can be tedious.  In Carneiro's mm1, I believe they can be proved 
using tactics.  

It felt like cheating for me to look at peano.mm1.  So I tried to limit
the number of times I consulted it, and I never actually used the mm1 
proof system.  However, it seems to have several advantages even
excluding the ability to write tactics.  For example, it appears to me
from looking at peano.mm1 that unification is a lot easier to deal with
there then in peano.mm.

(Commentary contributed by Patrick Brosnan, 10-Jun-2021.)


=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                          MORE PROPOSITIONAL VARIABLES
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

Solovay's peano.mm starts with just a few propositional variables.
This seemed inconvenient.  So I added some more.

$)

$v phi0 phi1 phi2 psi0 psi1 psi2 chi0 chi1 chi2 tau tau0 tau1 tau2 theta theta0 theta1 theta2 eta eta0 eta1 eta2 $.
wff_phi0 $f wff phi0 $.
wff_phi1 $f wff phi1 $.
wff_phi2 $f wff phi2 $.
wff_psi0 $f wff psi0 $.
wff_psi1 $f wff psi1 $.
wff_psi2 $f wff psi2 $.
wff_chi0 $f wff chi0 $.
wff_chi1 $f wff chi1 $.
wff_chi2 $f wff chi2 $.
wff_tau $f wff tau $.
wff_tau0 $f wff tau0 $.
wff_tau1 $f wff tau1 $.
wff_tau2 $f wff tau2 $.
wff_theta $f wff theta $.
wff_theta0 $f wff theta0 $.
wff_theta1 $f wff theta1 $.
wff_theta2 $f wff theta2 $.
wff_eta $f wff eta $.
wff_eta0 $f wff eta0 $.
wff_eta1 $f wff eta1 $.
wff_eta2 $f wff eta2 $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                           TAUTOLOGIES NOT USING NOT
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

These are tautologies (theorems of propositional logic) which can be stated
without the "not" operator, and proved without using ax-3.  

$)

${
 ax2d.1 $e  |- implies phi implies psi chi $.
 $( Deduction form of ax-2.  
    (Contributed by Patrick Brosnan, 18-Apr-2021.) $)
 ax2d   $p  |- implies
                 implies phi psi
                 implies phi chi  $=
   ( logbinopimplies wff_logbinop ax-2 ax-mp ) EECBFAFEECAFEBAFFDABCGH $.
$}


${ 
  mp2.1 $e |- phi $.
  mp2.2 $e |- psi $.
  mp2.3 $e |- implies phi
                      implies psi chi $.
  $( Double modus ponens inference copied from set.mm. Original
     by NM (= Norman Megill). Copy by Patrick Brosnan 7-Apr-2017 
     (Contributed by Patrick Brosnan, 8-Apr-2021.) $)
  mp2   $p |- chi $=
    ( logbinopimplies wff_logbinop ax-mp ) BCEAGCBHDFII $.
$}

${
   mp2b.1 $e |- phi $.
   mp2b.2 $e |- implies phi psi $.
   mp2b.3 $e |- implies psi chi $.
   $( A copy of a double mp from set.mm due to Carneiro. 
      (Contributed by Patrick Brosnan, 7-Apr-2021.) $)
   mp2b $p |- chi $=
     ( ax-mp ) BCABDEGFG $.
$}


${
 mpd.1 $e |- implies phi psi $.
 mpd.2 $e |- implies phi 
                     implies psi chi $.
 $( Yet another mp deduction copied from set.mm.
    Original by NM.  
     (Contributed by Patrick Brosnan, 7-Apr-2021.) $)
  mpd $p |- implies phi chi $=
    ( logbinopimplies wff_logbinop ax-2 ax-mp ) FBAGZFCAGZDFFCBGAGFKJGEABCHII
    $. 
$}

$( Principle of identity copied from set.mm. 
   (Original by NM. Copy by Patrick Brosnan 07-April-2017) 
     (Contributed by Patrick Brosnan, 7-Apr-2021.) $) 
  id $p |- implies phi phi $=
    ( logbinopimplies wff_logbinop ax-1 mpd ) ABAACZAAADAFDE $. 


${
  iffcomd.1 $e |- iff phi psi $.
  $( Deduction form of a result to commute iff statements. 
     (Contributed by Patrick Brosnan, 8-Apr-2021.) 

     WARNING: This is not a deduction form in the
     terminology of set.mm.  It is an inference.  I named it 
     when I had a very shaky understanding of the "deduction 
     theorem" and an even shakier understanding of the terminology
     surrounding it in set.mm.  So the name
     should be something like iffcomi.  In set.mm the corresponding
     result is called bicomi.

     (Commentary added by Patrick Brosnan, 19-Jul-2021.) 

     $) 
  iffcomd   $p |- iff psi phi $=
    ( logbinopimplies wff_logbinop logbinopiff bi1 ax-mp bi2 bi3 ) DBAEZFABEZFB
    AEZKCABGHDABEZDLKEMNCABIHBAJHH $.
$}

${
 a1i.1 $e |- phi $.
 $( Inference using antecedent copied from set.mm. 
    (Contributed by Patrick Brosnan, 8-Apr-2021.) $)
 a1i   $p |- implies psi phi $=
   ( logbinopimplies wff_logbinop ax-1 ax-mp ) ADABECABFG $. 
$}

${
syl.1  $e |- implies phi psi $.
syl.2 $e |- implies psi chi $.
$( Syllogism.  Copied, of course, from set.mm.  I think you can't do
   much without this one. 
   (Contributed by Patrick Brosnan, 8-Apr-2021.) $)
syl    $p |- implies phi chi $=
  ( logbinopimplies wff_logbinop a1i ax-2 ax-mp ) FBAGZFCAGZDFFCBGZAGFLKGMAEHAB
  CIJJ $. 
$}


$( Theorem form of ax-mp. 
   (Contributed by Patrick Brosnan, 22-Apr-2021.) $)
mpthm     $p |- implies phi implies implies phi psi psi $=
  ( logbinopimplies wff_logbinop ax-1 id ax-2 ax-mp syl ) ACACBADZDZCBJDZAJECJJ
  DCLKDJFJABGHI $.



${
sylant.1 $e |- implies phi implies psi chi $.
sylant.2 $e |- implies phi implies chi tau $.
$( Syllogism with antecedent. 
   (Contributed by Patrick Brosnan, 24-Apr-2021.) $)
sylant   $p |- implies phi implies psi tau $=
  ( logbinopimplies wff_logbinop ax-1 ax-2 syl mpd ) AGCBHZGDBHZEAGDCHZGNMHZFOG
  OBHPOBIBCDJKKL $.
$}

${
  a1id.1 $e |- implies phi psi $.
  $( Deduction form of a1i. Probably unecessary.  
     (Contributed by Patrick Brosnan, 24-Apr-2021.) $)
  a1id   $p |- implies phi implies chi psi $=
    ( logbinopimplies wff_logbinop ax-1 syl ) ABEBCFDBCGH $.
$}




${
comd.1 $e |- implies phi implies psi chi $. 
$( comd. An import thing stolen from metamath 
   (Contributed by Patrick Brosnan, 21-Apr-2021.) $)
comd   $p |- implies psi implies phi chi $=
  ( logbinopimplies wff_logbinop ax-1 ax2d syl ) BEBAFECAFBAGABCDHI $.
$}

$( The theorem form of comd. 
   (Contributed by Patrick Brosnan, 24-Apr-2021.) $)
com   $p |- implies implies phi implies psi chi
                 implies psi implies phi chi $=
  ( logbinopimplies wff_logbinop ax-1 a1i ax-2 sylant ) DDCBEAEZBDBAEZDCAEDKBEJ
  BAFGABCHI $.


$( Syllogism Theorem Reverse 
   (Contributed by Patrick Brosnan, 23-Apr-2021.) $)
sylthmr  $p |- implies implies psi chi 
                     implies implies phi psi 
                             implies phi chi $=
  ( logbinopimplies wff_logbinop ax-1 ax-2 syl ) DCBEZDIAEDDCAEDBAEEIAFABCGH $.



$( Syllogism Theorem 
   (Contributed by Patrick Brosnan, 24-Apr-2021.) $)
sylthm  $p |- implies implies phi psi 
                     implies implies psi chi
                             implies phi chi $=
  ( logbinopimplies wff_logbinop sylthmr comd ) DCBEDBAEDCAEABCFG $.


${
 syla1i.1 $e |- implies phi psi $.
 $( Like a1i but with syllogism. 
    (Contributed by Patrick Brosnan, 17-Apr-2021.) $)
 syla1i   $p |- implies phi implies chi psi $=
   ( logbinopimplies wff_logbinop ax-1 syl ) ABEBCFDBCGH $.
$}

${
pm2.43.1  $e |- implies phi implies phi psi $.
pm2.43    $p |- implies phi psi $=
  ( logbinopimplies wff_logbinop id ax-2 ax-mp ) DAAEZDBAEZAFDJAEDJIECAABGHH $.
$}

${
ded-iff1.1   $e |- iff phi psi $.
$( Deduction form of bi1. Eliminates a use of modus ponens. 
   (Contributed by Patrick Brosnan, 18-Apr-2021.) $)
ded-iff1     $p |- implies phi psi $=
  ( logbinopiff wff_logbinop logbinopimplies bi1 ax-mp ) DBAEFBAECABGH $.
$}

${
ded-iff2.1  $e |- iff phi psi $.
$( Deduction form of bi2. Eliminates a use of modus ponens. 
   (Contributed by Patrick Brosnan, 18-Apr-2021.) $)
ded-iff2    $p |- implies psi phi  $=
  ( logbinopiff wff_logbinop logbinopimplies bi2 ax-mp ) DBAEFABECABGH $. 
$}

sym-iff $p |- implies iff phi psi
                      iff psi phi $=
  ( logbinopiff wff_logbinop logbinopimplies bi1 bi2 bi3 syl mpd ) CBADZEBADZCA
  BDZABFKEABDEMLDABGBAHIJ $. 

${
symiffd.1 $e |- iff phi psi $.
$( Deduction for sym-iff. 
   (Contributed by Patrick Brosnan, 30-Apr-2021.) $) 
symiffd    $p |- iff psi phi $=
  ( logbinopiff wff_logbinop sym-iff ax-mp ) DBAEDABECABFG $.
$}

${
iff-ded.1  $e |- implies phi psi $.
iff-ded.2  $e |- implies psi phi $.
$( Proving iff by proving both directions. 
   (Contributed by Patrick Brosnan, 18-Apr-2021.) $)
iff-ded    $p |- iff phi psi $=
  ( logbinopimplies wff_logbinop logbinopiff bi3 ax-mp ) EABFZGBAFZDEBAFEKJFCAB
  HII $.
$}

${
bi3d.1 $e |- implies phi implies psi chi $.
bi3d.2 $e |- implies phi implies chi psi $.
$( Deduction form of bi3. 
   (Contributed by Patrick Brosnan, 19-Apr-2021.) $)
bi3d    $p |- implies phi iff psi chi $=
  ( logbinopimplies wff_logbinop logbinopiff bi3 syl mpd ) AFBCGZHCBGZEAFCBGFML
  GDBCIJK $.
$} 



${
iff-syl.1  $e |- iff phi psi $.
iff-syl.2  $e |- iff psi chi $.
$( Syllogism for iff.  
   (Contributed by Patrick Brosnan, 18-Apr-2021.) $)
iff-syl    $p |- iff phi chi $=
  ( ded-iff1 syl ded-iff2 iff-ded ) ACABCABDFBCEFGCBABCEHABDHGI $.
$}





${
iffsyl3.1 $e |- iff phi psi $.
iffsyl3.2 $e |- iff psi chi $.
iffsyl3.3 $e |- iff chi tau $.
$( Brings 3 iff equivalences together.  Might be useful. 
   (Contributed by Patrick Brosnan, 30-Apr-2021.) $) 
iffsyl3   $p |- iff phi tau $=
  ( iff-syl ) ACDABCEFHGH $.
$}

${
syl3.1 $e |-  implies phi psi $.
syl3.2 $e |-  implies psi chi $.
syl3.3 $e |-  implies chi tau $.
$( Brings 3  equivalences together.  Might be useful. 
   (Contributed by Patrick Brosnan, 30-Apr-2021.) $) 
syl3   $p |-  implies phi tau $=
  ( syl ) ABDEBCDFGHH $.
$}




${
iffmp.1  $e |- phi $.
iffmp.2  $e |- iff phi psi $.
$( Modus ponens for iff. Might be useful. 
   (Contributed by Patrick Brosnan, 18-Apr-2021.) $)
iffmp    $p |- psi $=
  ( logbinopiff wff_logbinop logbinopimplies bi1 ax-mp ) ABCEBAFGBAFDABHII $.
$}

${
iffmpr.1  $e |- psi $.
iffmpr.2  $e |- iff phi psi $.
$( Modus ponens for iff with phi and psi switched. 
Might also  be useful. 
    
   (Contributed by Patrick Brosnan, 20-Jun-2021.) $)
iffmpr    $p |- phi $=
  ( logbinopiff wff_logbinop logbinopimplies bi2 ax-mp ) BACEBAFGABFDABHII $.
$}



$( If and only if form of com 
   (Contributed by Patrick Brosnan, 24-Apr-2021.) $)
comiff $p |- iff    implies phi implies psi chi
                 implies psi implies phi chi $=
  ( logbinopimplies wff_logbinop com iff-ded ) DDCBEAEDDCAEBEABCFBACFG $.

$( Converse of ax-2. 
   (Contributed by Patrick Brosnan, 24-Apr-2021.) $)
ax2r  $p |- implies implies implies phi psi
                            implies phi chi
                    implies phi implies psi chi $=
  ( logbinopimplies wff_logbinop ax-1 a1i id sylant com syl ) DDCAEZDBAEZEZDLBE
  DDCBEAENBMLDMBENBAFGNHIBACJK $. 

$( If and only if version of ax-2. 
   (Contributed by Patrick Brosnan, 24-Apr-2021.) $)
ax2iff $p |- iff
              implies phi implies psi chi
              implies
                 implies phi psi
                 implies phi chi  $=
  ( logbinopimplies wff_logbinop ax-2 ax2r iff-ded ) DDCBEAEDDCAEDBAEEABCFABCGH
  $.

${
sylded.1 $e |- implies psi chi $.
$( A deduction from syl kind of like ax-2 as well. 
   (Contributed by Patrick Brosnan, 24-Apr-2021.) $)
sylded   $p |- implies implies phi psi
                       implies phi chi $=
  ( logbinopimplies wff_logbinop sylthmr ax-mp ) ECBFEECAFEBAFFDABCGH $.
$}

$( Theorem to replace antecedent with equivalent statement. 
   (Contributed by Patrick Brosnan, 25-Apr-2021.) $)  

iffleft $p |- implies iff phi psi
                      iff implies psi chi
                          implies phi chi $=
  ( logbinopiff wff_logbinop logbinopimplies bi1 sylthm syl bi2 bi3d ) DBAEZFCB
  EZFCAEZLFBAEFNMEABGABCHILFABEFMNEABJBACHIK $.

${
iffleftd.1 $e |- iff phi psi $.
$( Deduction from iffleft . 
   (Contributed by Patrick Brosnan, 25-Apr-2021.) $)
iffleftd   $p |- iff implies psi chi 
                     implies phi chi $=
  ( logbinopiff wff_logbinop logbinopimplies iffleft ax-mp ) EBAFEGCAFGCBFFDABC
  HI $.
$}

$( Theorem to replace conclusion with equivalent statement. 
   (Contributed by Patrick Brosnan, 25-Apr-2021.) $)
iffright $p |- implies iff psi chi
                       iff implies phi psi
                           implies phi chi $=
  ( logbinopiff wff_logbinop logbinopimplies bi1 sylthmr syl bi2 bi3d ) DCBEZFB
  AEZFCAEZLFCBEFNMEBCGABCHILFBCEFMNEBCJACBHIK $.

${
  iffrightd.1 $e |- iff psi chi $.
  $( Deduction form of iffright. 
   (Contributed by Patrick Brosnan, 25-Apr-2021.) $)
iffrightd   $p |-   iff implies phi psi
                        implies phi chi $=
  ( logbinopiff wff_logbinop logbinopimplies iffright ax-mp ) ECBFEGCAFGBAFFDAB
  CHI $.
$}

${
comantd.1 $e |- implies phi implies psi implies chi tau $.
$( Form of comd which just switches 2nd and 3rd positions. 
   (Contributed by Patrick Brosnan, 8-May-2021.) $)
comantd  $p |- implies phi implies chi implies psi tau $=
  ( logbinopimplies wff_logbinop com syl ) AFFDCGBGFFDBGCGEBCDHI $.
$}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   NEGATION 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

${
not-ded.1  $e |- implies phi implies not psi not chi $.
  $( Copied from set.mm. But I forgot the name. 
   (Contributed by Patrick Brosnan, 16-Apr-2021.) $)
not-ded    $p |- implies phi implies chi psi $=
  ( logbinopimplies wff_not wff_logbinop ax-3 syl ) AECFBFGEBCGDBCHI $.  
$}

${
pm2.21d.1 $e |- implies phi not psi $.
  $( Copied from set.mm.  With the correct name. 
   (Contributed by Patrick Brosnan, 17-Apr-2021.) $)
pm2.21d   $p |- implies phi implies psi chi $=
  ( logbinopimplies wff_not wff_logbinop syla1i ax-3 syl ) AEBFZCFZGECBGAKLDHCB
  IJ $.
$}

$( phi and not phi imply anything. Theorem form of pm2.21.d 
   (Contributed by Patrick Brosnan, 17-Apr-2021.) $)
contra $p |- implies not phi implies phi psi $=
  ( wff_not logbinopimplies wff_logbinop ax-1 ax-3 syl ) ACZDIBCZEDBAEIJFBAGH
  $. 

$( (not phi implies phi) implies phi.  Important technically for negation. 
   (Contributed by Patrick Brosnan, 18-Apr-2021.) $)
iinppp $p |- implies implies not phi phi 
                     phi  $=
  ( logbinopimplies wff_not wff_logbinop contra ax2d not-ded pm2.43 ) BAACZDZAJ
  AJIAJCZAKEFGH $.

$( phi implies (not phi implies phi) Easy converse of iinppp 
   (Contributed by Patrick Brosnan, 18-Apr-2021.) $)
pinpip $p |- implies phi
                     implies not phi phi $=
  ( wff_not ax-1 ) AABC $.

$( (not phi implies phi) iff phi 
   (Contributed by Patrick Brosnan, 18-Apr-2021.) $)
iffinppp  $p |- iff implies not phi phi 
                    phi $=
  ( logbinopimplies wff_not wff_logbinop iinppp pinpip iff-ded ) BAACDAAEAFG $.


${
ipnpd.1 $e |- implies not phi phi $.
$( Deduction for iffinppp. 
   (Contributed by Patrick Brosnan, 9-May-2021.) $)
ipnpd   $p |- phi $=
  ( logbinopimplies wff_not wff_logbinop iffinppp ded-iff1 ax-mp ) CAADEZABIAAF
  GH $.
$}



$( not not phi implies phi 
   (Contributed by Patrick Brosnan, 18-Apr-2021.) $)
innpp  $p |- implies not not phi phi $=
  ( wff_not logbinopimplies wff_logbinop ax-1 not-ded iinppp syl ) ABZBZCAIDAJA
  IJIEFAGH $.

$( phi implies not not phi 
   (Contributed by Patrick Brosnan, 18-Apr-2021.) $)
ipnnp  $p |- implies phi not not phi $=
  ( wff_not logbinopimplies wff_logbinop innpp a1i not-ded pm2.43 ) AABZBZAJACI
  JBDAIEFGH $.

$( phi iff not not phi 
   (Contributed by Patrick Brosnan, 18-Apr-2021.) $)
iffpnnp $p |- iff phi not not phi $=
  ( wff_not ipnnp innpp iff-ded ) AABBACADE $.

$( Reverse version of ax3 
   (Contributed by Patrick Brosnan, 24-Apr-2021.) $)
ax3r    $p |- implies implies phi psi implies not psi not phi $=
  ( logbinopimplies wff_logbinop wff_not innpp sylthm ax-mp ipnnp sylded ax-3
  syl ) CBADZCBAEZEZDZCNBEZDZCAODCPMDAFOABGHPCQEZODROBSBIJNQKLL $.

${
ax3rd.1 $e |- implies phi psi $. 
$( Deduction from reverse of ax3 
   (Contributed by Patrick Brosnan, 24-Apr-2021.) $)
ax3rd   $p |- implies not psi not phi $=
  ( logbinopimplies wff_logbinop wff_not ax3r ax-mp ) DBAEDAFBFECABGH $.
$}

$( If and only if form of ax-3 
   (Contributed by Patrick Brosnan, 24-Apr-2021.) $)
ax3iff  $p |- iff implies phi psi implies not psi not phi $=
  ( logbinopimplies wff_logbinop wff_not ax3r ax-3 iff-ded ) CBADCAEBEDABFBAGH
  $. 

$( (P -> (~ Q -> ~R)) <-> (P -> ( R -> Q)) 
   iff form of ax-3 with antecedent 
   (Contributed by Patrick Brosnan, 30-Apr-2021.) $)
ax3iffant  $p  |- iff implies phi implies not psi not chi
                      implies phi implies chi psi $=
  ( logbinopimplies wff_not wff_logbinop ax3iff iffcomd iffrightd ) ADCEBEFZDBC
  FZKJCBGHI $.


$( P <-> Q same as (not P) <-> (not Q) 
   (Contributed by Patrick Brosnan, 24-Apr-2021.) $)
iffnotr  $p |- iff iff phi psi
                   iff not psi not phi $=
  ( logbinopiff wff_logbinop wff_not logbinopimplies bi1 ax3r syl bi2 bi3d ax-3
  iff-ded ) CBADZCAEZBEZDZNPONFBADZFOPDZABGABHINFABDZFPODZABJBAHIKQABQSRPOGBALI
  QUATPOJABLIKM $. 

$( (P <-> Q) -> (Q <-> P).  Lemma for switching Ps and Qs. 
   (Contributed by Patrick Brosnan, 24-Apr-2021.) $)
iffcomlem $p |- implies iff phi psi
                        iff psi phi $=
  ( logbinopiff wff_logbinop bi2 bi1 bi3d ) CBADBAABEABFG $.

${
iffcomlemd.1 $e |- implies phi iff psi chi $.
$( Deduction form for iffcomlem.  Hopefully useful for iff-congr 
   (Contributed by Patrick Brosnan, 19-May-2021.) $)
iffcomlemd  $p |- implies phi iff chi psi $=
  ( logbinopiff wff_logbinop iffcomlem syl ) AECBFEBCFDBCGH $. 
$}

$( (P <-> Q) <-> (Q <-> P). Switches Ps and Qs. Or phi's and psi's. 
   (Contributed by Patrick Brosnan, 24-Apr-2021.) $)
iffcom    $p |- iff iff phi psi
                    iff psi phi $=
  ( logbinopiff wff_logbinop iffcomlem iff-ded ) CBADCABDABEBAEF $. 

$( P <-> Q same as (not P) <-> (not Q) 
   (Contributed by Patrick Brosnan, 24-Apr-2021.) $)
iffnot  $p |- iff iff phi psi
                  iff not phi not psi $=
  ( logbinopiff wff_logbinop wff_not iffnotr iffcom iff-syl ) CBADCAEZBEZDCJIDA
  BFJIGH $. 


${ 
iffnotd.1 $e |- iff phi psi $.
$( Deduction form of iffnot.  
   (Contributed by Patrick Brosnan, 24-Apr-2021.) $)
iffnotd   $p |- iff not phi not psi $=
  ( logbinopiff wff_logbinop wff_not iffnot iffmp ) DBAEDBFAFECABGH $. 
$}

$( iff form of pnotq 
   (Contributed by Patrick Brosnan, 26-Apr-2021.) $)
iffpnotq $p |- iff implies phi not psi 
                   implies psi not phi $=
  ( logbinopimplies wff_not wff_logbinop ax3iff iffpnnp iffleftd iff-syl ) CBDZ
  AECADZJDZECKBEAJFBLKBGHI $. 


$( ( P -> ~ Q) -> (Q -> ~ P).  Helpful negation theorem. 
   (Contributed by Patrick Brosnan, 26-Apr-2021.) $)
pnotq    $p |- implies implies phi not psi 
                       implies psi not phi $=
  ( logbinopiff logbinopimplies wff_not wff_logbinop iffpnotq bi1 ax-mp ) CDAEB
  FZDBEAFZFDJKFABGKJHI $.

$( ( ~ P -> Q) <-> ( ~ Q -> P).  Another helpful negation. 
   (Contributed by Patrick Brosnan, 29-Apr-2021.) $)
iffnotpq   $p |- iff  implies not phi psi
                      implies not psi phi $=
  ( logbinopimplies wff_not wff_logbinop ax3iff logbinopiff iffcomlem iffrightd
  iffpnnp ax-mp iff-syl ) CBADZECMDZBDZECAOEMBFONAGNAEGANEAJANHKIL $.

${
notpqi.1 $e |- implies not phi psi $.
$( ~P -> Q => ~Q -> P.  Useful later. 
   (Contributed by Patrick Brosnan, 15-Jun-2021.) $)
notpqi   $p |- implies not psi phi $=
  ( logbinopimplies wff_not wff_logbinop iffnotpq ded-iff1 ax-mp ) DBAEFZDABEFZ
  CJKABGHI $. 
$}



${
pnotqd.1   $e |- implies phi not psi $.
$( Deduction form of pnotq 
   (Contributed by Patrick Brosnan, 26-Apr-2021.) $)
pnotqd     $p |- implies psi not phi $=
  ( logbinopimplies wff_not wff_logbinop pnotq ax-mp ) DBEAFDAEBFCABGH $. 
$}

${
ax3rdant.1 $e |- implies phi implies psi chi $.
$( Deduction of ax3rd with antecedent. 
   (Contributed by Patrick Brosnan, 8-May-2021.) $)
ax3rdant   $p |- implies phi implies not chi not psi $=
  ( logbinopimplies wff_logbinop wff_not ax3r syl ) AECBFEBGCGFDBCHI $.
$}

${
pnppd.1 $e |- implies phi not phi $.
$( Deduction for iffinppp. 
   (Contributed by Patrick Brosnan, 9-May-2021.) $)
pnppd   $p |- not phi $=
  ( wff_not innpp syl ipnpd ) ACZGCAGADBEF $.
$}

${
ax3lemd.1 $e |- implies phi iff psi chi $.
$( Lemma for mostly for exinst. 
   (Contributed by Patrick Brosnan, 14-Jun-2021.) $)
ax3lemd   $p |- implies phi iff not psi not chi 
$=
  ( logbinopiff wff_logbinop wff_not iffnot ded-iff1 syl ) AECBFZECGBGFZDKLBCHI
  J $.
$}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   TRUTHINESS 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

   (Contributed by Patrick Brosnan, 12-Apr-2021.) $)

phi_imp_true   $p |- implies phi implies psi psi $=
  ( logbinopimplies wff_logbinop id ax-1 ax-mp ) CBBDZCHADBEHAFG $.

phi_imp_true_phi $p |- implies phi implies implies psi psi phi $=
  ( logbinopimplies wff_logbinop ax-1 ) ACBBDE $.

imp_true_phi_phi $p |- implies implies implies psi psi phi phi $=
  ( logbinopimplies wff_logbinop id ax-1 ax-mp mpd ) CACBBDZDZIAICIJDBEIJFGJEH
  $. 

${
provenot.1 $e |- implies phi not implies psi psi $.
$( Deduction for proving not phi. 
   (Contributed by Patrick Brosnan, 8-May-2021.) $)
provenot   $p |- not phi $=
  ( logbinopimplies wff_logbinop wff_not id pnotqd ax-mp ) DBBEZAFBGAJCHI $.
$}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   CONJUNCTIVITIS 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

   (Contributed by Patrick Brosnan, 25-Apr-2021.) $)


sym-an  $p |- iff  and phi psi
                   and psi phi $=
  ( wff_logbinop logbinopimplies wff_not df-an iffpnnp iffleftd iff-syl iffnotd
  logbinopand ax3iff iffcomd ) KBACZDAEZBCZEZKABCZNDBEZACZEQABFTPTDOSEZCPASLBUA
  OBGHIJIRQBAFMI $.

simp-an $p |- iff implies and phi psi
                          chi 
                   implies phi 
                           implies psi chi $=
  ( logbinopimplies wff_logbinop wff_not df-an symiffd iffleftd iffnotpq comiff
  logbinopand iffsyl3 ax3iffant iff-syl ) DCLBAEZEZDDBFZCFZEAEZDDCBEAEQDCDRAEZF
  ZEDUASETUBPCPUBABGHIUACJSARKMACBNO $.

${
simpand.1 $e |- implies and phi psi chi $.
$( Deduction from simp-an. 
   (Contributed by Patrick Brosnan, 30-Apr-2021.) $) 
simpand   $p |- implies phi implies psi chi $=
  ( logbinopimplies logbinopand wff_logbinop simp-an ded-iff1 ax-mp ) ECFBAGGZE
  ECBGAGZDKLABCHIJ $.
$}

${
simpandr.1 $e |- implies phi implies psi chi $.
$( Deducing P and Q implies R from implication form. 
   (Contributed by Patrick Brosnan, 8-May-2021.) $)
simpandr   $p |- implies and phi psi chi $=
  ( logbinopimplies wff_logbinop logbinopand simp-an ded-iff2 ax-mp ) EECBFAFZE
  CGBAFFZDLKABCHIJ $.
$}


${
andded.1 $e |- phi $.
andded.2 $e |- psi $.
andded.3 $e |- implies and phi psi 
                       chi $.
$( And deduction.  Convenience Theorem. 
   (Contributed by Patrick Brosnan, 30-Apr-2021.) $)
andded   $p |- chi $=
  ( logbinopimplies wff_logbinop logbinopand simp-an ded-iff1 ax-mp ) BCEAGCBHZ
  DGCIBAHHZGMAHZFNOABCJKLLL $. 
$}

${
anddant.1 $e |- implies phi psi $.
anddant.2 $e |- implies phi chi $.
$( Way to deduce psi and chi.  More important than andded above. 
   (Contributed by Patrick Brosnan, 2-May-2021.) $)
anddant   $p |- implies phi and psi chi $=
  ( logbinopand wff_logbinop logbinopimplies id simp-an ded-iff1 ax-mp syl comd
  pm2.43 ) AFCBGZACHPAGEACPABHPCGZDHPPGZHQBGZPIRSBCPJKLMNMO $.
$}

$( Corollary of simp-an for deducing and phi psi. 
   (Contributed by Patrick Brosnan, 7-May-2021.) $)
andthm $p |- implies phi 
                     implies psi and phi psi $=
  ( logbinopimplies logbinopand wff_logbinop id simp-an iffmp ) CDBAEZIECCIBEAE
  IFABIGH $.

${
andd.1 $e |- phi $.
andd.2 $e |- psi $.
$( Pure deduction of anddant 
   (Contributed by Patrick Brosnan, 2-May-2021.) $)
andd   $p |- and phi psi $=
  ( logbinopand wff_logbinop id a1i anddant ax-mp ) AEBAFCAABAGBADHIJ $.
$}

$( Theorem to get phi from phi and psi. 
   (Contributed by Patrick Brosnan, 6-May-2021.) $)
andleft $p |- implies and phi psi 
                      phi $=
  ( logbinopimplies wff_logbinop logbinopand ax-1 logbinopiff simp-an bi2 ax-mp
  ) CCABDADZCAEBADDZABFGKLDCLKDABAHLKIJJ $.

$( Theorem to get psi from phi and psi. $) 
andright $p |- implies and phi psi 
                       psi $=
( logbinopand wff_logbinop logbinopiff logbinopimplies sym-an bi1 andleft syl
  ax-mp ) CBADZCABDZBEMLDFMLDABGLMHKBAIJ $. 

${
andimpd.1 $e |- implies phi1 phi2 $.
andimpd.2 $e |- and phi1 psi $.
$( Deduction for getting implication through and. 
   (Contributed by Patrick Brosnan, 7-May-2021.) $)
andimpd   $p |- and phi2 psi $=
  wff_phi2 wff_psi wff_phi1 wff_phi2 logbinopand wff_psi wff_phi1 wff_logbinop
  wff_phi1 andimpd.2 wff_phi1 wff_psi andleft ax-mp andimpd.1 ax-mp logbinopand
  wff_psi wff_phi1 wff_logbinop wff_psi andimpd.2 wff_phi1 wff_psi andright
  ax-mp andd $.
$}

notpanp $p |- not and phi not phi $=
  ( logbinopand wff_not wff_logbinop logbinopimplies ax3rdant simpandr provenot
  ax-1 ) BACZADAAJEAADZCAKAAKIFGH $. 


andcom $p |- implies and phi psi and psi phi $=
  ( logbinopand wff_logbinop id simpand comd simpandr ) ABCABDZBAIBAIIEFGH $.

${
andcomd.1 $e |- and phi psi $.
$( Deduction for andcom. 
   (Contributed by Patrick Brosnan, 8-May-2021.) $)
andcomd   $p |- and psi phi $=
  ( logbinopand wff_logbinop andcom ax-mp ) DBAEDABECABFG $.
$}

andcomiff $p |- iff and phi psi and psi phi $=
  ( logbinopand wff_logbinop andcom iff-ded ) CBADCABDABEBAEF $.

andass $p |- implies and and phi psi chi
                     and phi and psi chi $=
  ( logbinopand wff_logbinop logbinopimplies id simpand comd comantd simpandr )
  DBAECDDCBEZAEZABFMCEZBANBCAMBCFMAEALMALMMGHIHJIKK $.

${
andassrtd.1 $e |- and and phi psi chi $.
$( Deduction for moving parentheses to right. 
   (Contributed by Patrick Brosnan, 8-May-2021.) $)
andassrtd   $p |- and phi and psi chi $=
  ( logbinopand wff_logbinop andass ax-mp ) ECEBAFFEECBFAFDABCGH $.
$}

${
andimprd.1 $e |- implies psi1 psi2 $.
andimprd.2 $e |- and phi psi1 $.
$( Deduction for getting implication through and commuted. 
     
   (Contributed by Patrick Brosnan, 9-May-2021.) $)
andimprd   $p |- and phi psi2 $=
  ( andcomd andimpd ) CAABCDABEFGF $. 
$}


${
pandcomd.1  $e |- and phi and psi chi $.
$( Commutation with antecedent in and:  P /\ (Q /\ R) = Q /\ (R /\ Q). 
   (Contributed by Patrick Brosnan, 8-May-2021.) $)
pandcomd    $p |- and phi and chi psi $=
  ( logbinopand wff_logbinop andcom andimprd ) AECBFEBCFBCGDH $. 
$}

andassiff $p |- iff and and phi psi chi 
                    and phi and psi chi $=
  ( logbinopand wff_logbinop andass logbinopimplies id simpand comantd simpandr
  comd iff-ded ) DCDBAEZEZDDCBEZAEABCFAPOPAOBCGOAEBACOABGOCEZABQNCOOHIILJKLKM
  $.

${
andasslfd.1  $e |- and phi and psi chi $.
$( Deduction for moving parentheses to the left. 
   (Contributed by Patrick Brosnan, 8-May-2021.) $)
andasslfd    $p |- and and phi psi chi $=
  ( logbinopand wff_logbinop andassiff ded-iff2 ax-mp ) EECBFAFZECEBAFFZDKJABCG
  HI $.
$}

${
anprvnotd.1 $e |- implies phi psi $.
anprvnotd.2 $e |- implies phi not psi $.
$( Deduction to prove not phi. 
   (Contributed by Patrick Brosnan, 9-May-2021.) $) 
anprvnotd   $p |- not phi $=
  ( wff_not logbinopimplies wff_logbinop contra syl comd pm2.43 pnppd ) AAAEZAB
  FMAGCABMABEFMBGDBMHIJIKL $.
$}


andimpthm $p |- implies implies phi psi
                        implies and phi chi and psi chi $=
  ( logbinopimplies wff_logbinop logbinopand andright andleft syl mpd anddant
  simpand ) DBAEZFCAEZFCBEFNMEZBCOABONAMNGZACHIMNHJONCPACGIKL $.




${
andimpthma.1 $e |- implies phi implies psi1 psi2 $.
$( And in an implication but with antecdent. 
   (Contributed by Patrick Brosnan, 14-May-2021.) $)
andimpthma   $p |- implies phi 
                      implies and psi1 chi and psi2 chi $=
  ( logbinopimplies wff_logbinop logbinopand andimpthm a1i mpd ) AFDCGZFHBDGHBC
  GGZEFMLGACDBIJK $.
$}


$( Theorem to get iff from and. 
   (Contributed by Patrick Brosnan, 14-May-2021.) $)
andiffthm $p |- implies iff phi1 phi2 
                        iff and phi1 psi and phi2 psi $=
  ( logbinopiff wff_logbinop logbinopand logbinopimplies bi1 andimpthm syl bi3d
  bi2 ) DCBEZFABEZFACEZMGCBEGONEBCHBCAIJMGBCEGNOEBCLCBAIJK $.



${
contrad.1 $e |- implies phi psi $.
contrad.2 $e |- implies phi not psi $.
$( Deduction form of contra. 
   (Contributed by Patrick Brosnan, 19-Jun-2021.) $)
contrad   $p |- implies phi chi $=
  ( logbinopand wff_not wff_logbinop anddant contra simpandr syl ) AFBBGZHCAMBE
  DIMBCBCJKL $.
$}

${
notcontrad.1 $e |- implies phi psi $.
notcontrad.2 $e |- implies phi not psi $.
$( Another deduction from contra. 
   Same as anprvnotd.  Didn't see it originally.
   (Contributed by Patrick Brosnan, 20-Jun-2021.) $)
notcontrad  $p |- not phi $=
  ( wff_not contrad pnppd ) AABAECDFG $.
$}



$(

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                    MORE PROPOSITIONS 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

$)


${
iffsyld.1  $e |- implies phi iff psi chi $.
iffsyld.2  $e |- implies phi iff chi tau $.
$( Deduction Syllogism for iff.  
   (Contributed by Patrick Brosnan, 18-Apr-2021.) $)
iffsyld    $p |- implies phi iff psi tau $=
  ( logbinopiff wff_logbinop logbinopimplies bi1 syl sylant bi2 bi3d ) ABDABCDA
  GCBHZICBHEBCJKAGDCHZIDCHFCDJKLADCBAPICDHFCDMKAOIBCHEBCMKLN $.
$}


$( Iff Syllogism Theorem 
   (Contributed by Patrick Brosnan, 18-May-2021.) $)
iffsylt  $p |- implies iff phi psi 
                         implies iff psi chi
                                 iff phi chi $=
  ( logbinopiff wff_logbinop logbinopand andleft andright iffsyld simpand ) DBA
  EZDCBEZDCAEFLKEABCKLGKLHIJ $.



${
iff-congrd.1 $e |- implies phi iff psi0 psi1 $.
iff-congrd.2 $e |- implies phi iff chi0 chi1 $.
$( eq-congr, but for iff, and in deduction form. 
   (Contributed by Patrick Brosnan, 19-May-2021.) $)

prop-congrlemd  $p |- implies phi implies implies psi0 chi0
                                          implies psi1 chi1 $=
  ( logbinopimplies wff_logbinop logbinopiff bi1 syl sylthmr bi2 sylthm sylant
  ) AHDBIZHEBIZHECIZAHEDIZHRQIAJEDITGDEKLBDEMLAHBCIZHSRIAJCBIUAFBCNLCBEOLP $. 

prop-congrd     $p |- implies phi iff implies psi0 chi0
                                     implies psi1 chi1 $=
  ( logbinopimplies wff_logbinop prop-congrlemd iffcomlemd bi3d ) AHDBIHECIABCD
  EFGJACBEDABCFKADEGKJL $. 

iff-congrlemd $p |- implies phi implies iff psi0 chi0
                                        iff psi1 chi1 $=
  ( logbinopiff wff_logbinop logbinopimplies iffcomlemd iffsylt syl comd sylant
  ) AHDBIZHDCIZHECIZAHBCIJQPIABCFKCBDLMAHEDIZJRQIGQSRCDELNMO $.

iff-congrd   $p |- implies phi iff iff psi0 chi0
                                   iff psi1 chi1 $=
  ( logbinopiff wff_logbinop iff-congrlemd iffcomlemd bi3d ) AHDBIHECIABCDEFGJA
  CBEDABCFKADEGKJL $.
$}

${
indlem.1  $e |- implies phi iff psi chi $.
indlem.2  $e |- chi $.
$( Lemma which will hopefully be useful for induction. 
   (Contributed by Patrick Brosnan, 27-May-2021.) $)
indlem    $p |- implies phi psi $=
  ( logbinopimplies wff_logbinop logbinopiff bi2 syl comd ax-mp ) CFBAGEACBAHCB
  GFBCGDBCIJKL $.
$}

prop-refl $p |- iff phi phi $=
  ( id iff-ded ) AAABZDC $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                                PEANO ARITHMETIC
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                MORE LETTER VARIABLES AND TERMS  
=-=-=-=-=-=-=-==-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

The original file peano.mm has only a few names
for variables (v, x, y and z) and a few names
for terms (s, t, u along with s0, s1 and t0, t1).
It seems wise to expand these in a sensible way.

We could do a Greek letter, roman letter split.
But it seems that first it might be good just to
let every letter in the alphabet not already 
designated as a variable be a term.  
So a, b, c, etc are all terms.  
Then, we can let va, vb, vc, etc all be variables.
That way we will hopefully keep straight which is 
which.

For future reference, it might help to remember
the simple shell script that produced the long list:

  for i in {a..z}; do echo "term$i \$f term $i"; done

That produced the list for the terms and then I culled
it by hand. The one with the variables with produced
by substituting "{a..z}" with just "va, vb, ..., "

Anyway, here goes.

(Commentary contributed by Patrick Brosnan, 10-Jun-2021.)

$)

$v a b c d e f g h i j k l m n o p q r w $.
$v va vb vc vd ve vf vg vh vi vj vk vl vm vn vo vp
   vq vr vs vt vu vw $. 


terma $f term a $.
termb $f term b $.
termc $f term c $.
termd $f term d $.
terme $f term e $.
termf $f term f $.
termg $f term g $.
termh $f term h $.
termi $f term i $.
termj $f term j $.
termk $f term k $.
terml $f term l $.
termm $f term m $.
termn $f term n $.
termo $f term o $.
termp $f term p $.
termq $f term q $.
termr $f term r $.
termw $f term w $.


varva $f var va $.
varvb $f var vb $.
varvc $f var vc $.
varvd $f var vd $.
varve $f var ve $.
varvf $f var vf $.
varvg $f var vg $.
varvh $f var vh $.
varvi $f var vi $.
varvj $f var vj $.
varvk $f var vk $.
varvl $f var vl $.
varvm $f var vm $.
varvn $f var vn $.
varvo $f var vo $.
varvp $f var vp $.
varvq $f var vq $.
varvr $f var vr $.
varvs $f var vs $.
varvt $f var vt $.
varvu $f var vu $.
varvw $f var vw $.

$(

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                    QUANTIFIERS AND SUCH (mostly universal)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

This is the first pass at quantifiers.  I am not 100% sure but 
I think the axioms in set.mm are simpler and also closer to being
metalogically complete than the axioms here.  As an example,
ax-4 of set.mm is quantified implications, which says that 

    forall x (phi -> psi) -> (forall x phi -> forall x psi).

My guess is that this axiom is not provable in peano.mm. 
Of course, it is (certainly) provable in every particular 
instance when phi and psi are replaced with formulas involving
no propositional (wff) variable.   But my guess is that the 
proof involves the considerations of substitution discussed
by Solovay in setting up peano.mm.  So I think the length
of the (shortest) probably grows (hopefully logarithmically) 
in the length of the formulas involved. 

This section does, however, prove the axioms of generalization
and distinctness from set.mm.  Still, working with peano.mm
makes me appreciate the handling of quantifiers in set.mm.
One thing that is particularly nice is that the axiom of 
distinctness in set.mm is the only logical axiom which uses
a disjoint variable assumption. 

Later, after we prove the basic algebraic properties of
Peano Arithmetic, we are going to have to come back to 
quantifiers again to fight with the existential quantifier.


(Commentary contributed by Patrick Brosnan, 14-Jun-2021.)

$)

${
gen.1 $e |- phi $.
$( Generalization.  
   (Contributed by Patrick Brosnan, 3-May-2021.) $)
gen   $p |- forall x phi $=
  tzero tzero binpred_equals wff_atom varx quant_all wff_phi wff_quant tzero
  eq-refl varx tzero tzero binpred_equals wff_atom wff_phi wff_phi tzero tzero
  binpred_equals wff_atom gen.1 a1i alpha_2 ax-mp $.
$}

${
subswlla.1 $e |- implies = s t phi $.
$( Lemma for switching orders of things in substl. 
   (Contributed by Patrick Brosnan, 28-May-2021.) $) 
subswlla   $p |- implies = t s phi $=
  ( binpred_equals wff_atom eq-sym syl ) BAEFABEFCBAGDH $.
$}

${
subswl.1 $e |- implies = s t iff phi psi $.
$( Lemma using subswla to switch orders in substl. 
   (Contributed by Patrick Brosnan, 28-May-2021.) $)
subswl   $p |- implies = t s iff psi phi $=
  ( binpred_equals wff_atom logbinopiff wff_logbinop subswlla iffcomlemd ) BAFG
  CDABHDCIEJK $.
$}

${
$d y t $.
$d y psi $.
substl.1  $e |- implies = y t iff phi psi $.
$( Substitution lemma. Hopefully useful for induction. 
   (Contributed by Patrick Brosnan, 27-May-2021.) $)
substl    $p |- iff forall y implies = y t phi
                    psi $=
  ( quant_all logbinopimplies binpred_equals wff_logbinop wff_quant logbinopiff
  tvar wff_atom all_elim3 bi2 syl comd alpha_2 iff-ded ) BFGCBLAHMZIZJDABCDENBD
  UATDCTKDCIGCDIECDOPQRS $.
$}

${
alpha1i.1   $e |- iff phi psi $.
$( Inference form of alpha_1 without the antecedent. 
   (Contributed by Patrick Brosnan, 27-May-2021.) $)
alpha1i     $p |- iff quant x phi quant x psi $=
  ( tzero binpred_equals logbinopiff wff_quant wff_logbinop eq-refl a1i alpha_1
  wff_atom ax-mp ) FFGNZHABDIABCIJFKABPCDHDCJPELMO $.
$}

${
$d x phi $.
$( The axiom of distinctness.  Or ax-5 from set.mm. 
   (Contributed by Patrick Brosnan, 27-May-2021.) $)
dist $p |- implies phi forall x phi $=
  ( id alpha_2 ) ABBBCD $.
$}


${
$d x t $.
$d x psi $.
vswpmp.1  $e |- phi $.
vswpmp.2  $e |- implies = x t iff phi psi $.
$( Modus ponens with variable swap. 
   (Contributed by Patrick Brosnan, 28-May-2021.) $) 
vswpmp    $p |- psi $=
  ( quant_all logbinopimplies binpred_equals wff_atom wff_logbinop gen all_elim
  tvar wff_quant ax-mp all_elim3 ) BGHCBNAIJKOZDBGCORBCELABCMPABCDFQP $.
$}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                    TERM ELIMINATION
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

   (Contributed by Patrick Brosnan, 30-Apr-2021.) $)

eq-sym-iff $p |- iff = s t = t s $=
  ( binpred_equals wff_atom eq-sym iff-ded ) ABCDBACDABEBAEF $.

${
eq-sym-d.1 $e |- = s t $.
$( Deduction from eq-sym. 
   (Contributed by Patrick Brosnan, 2-May-2021.) $)
eq-sym-d   $p |- = t s $=
  ( binpred_equals wff_atom eq-sym ax-mp ) ABDEBADECABFG $.
$}

ne-sym-iff $p |- iff not = s t not = t s $=
  ( binpred_equals wff_atom eq-sym-iff iffnotd ) ABCDBACDABEF $.

${
ne-sym-d.1 $e |- not = s t $.
$( Deduction from ne-sym-iff. $)
ne-sym-d   $p |- not = t s $=
( binpred_equals wff_atom wff_not ne-sym-iff ded-iff1 ax-mp ) ABDEFZBADEFZCJK
  ABGHI $.
$}

lemstu $p |- implies = s t
                     iff not = s u 
                         not = t u $=
  ( binpred_equals logbinopimplies logbinopiff wff_not wff_logbinop logbinopand
  wff_atom eq-refl eq-congr iffnot ded-iff1 syl simpand comd ax-mp ) CCDJZEFBCD
  JZGACDJZGHZABDJZHCKUCSUBUCSUBISUCHFTUAHZUBABCCDLUDUBUATMNOPQR $.

lemstur $p |- implies = s t iff not = u s 
                               not = u t $=
  ( binpred_equals logbinopimplies logbinopiff wff_not wff_logbinop logbinopand
  wff_atom eq-refl eq-congr iffnot ded-iff1 syl simpand ax-mp ) CCDJZEFCBDJZGCA
  DJZGHZABDJZHCKRUBUAIUBRHFSTHZUACCABDLUCUATSMNOPQ $. 

${
$d t x $. 
pa_ax1t $p |- not = 0 S t $=
  ( varx tsucc tzero quant_all logbinopimplies tvar binpred_equals wff_logbinop
  wff_atom wff_not wff_quant eq-refl pa_ax1 ne-sym-d alpha_2 logbinopiff eq-suc
  a1i ax-mp lemstu syl all_elim3 ) ACZDBEFBGZCZDHJKZUEAHJZIZLZUDDHJKZDDHJZUJDMB
  ULUIUIULUGUHDUFBNOSSPTABUGUKUHUFUDHJQUKUGIUEARUFUDDUAUBUCTO $.
$}

pa_ax1tb $p |- not = 0 S t $=
  tt pa_ax1t $.

pa_ax1tcor $p |- not = S x 0 $=
  tzero varx tvar tsucc varx tvar pa_ax1t ne-sym-d $.

${
eq-congrd.1 $e |- implies phi = s0 s1 $.
eq-congrd.2 $e |- implies phi = t0 t1 $. 
$( Deduction from eq-congr. 
   (Contributed by Patrick Brosnan, 18-May-2021.) $)
eq-congrd   $p |- implies phi
                          iff binpred s0 t0
                              binpred s1 t1 $=
  ( logbinopand binpred_equals wff_atom wff_logbinop logbinopiff eq-congr syl
  anddant ) FICDJKZABJKZLMBDEKACEKLFRQGHPABCDENO $.
$}

${
e-congrd.1 $e |- implies phi = s0 s1 $.
e-congrd.2 $e |- implies phi = t0 t1 $. 
$( Form of eq-congrd with binpred replaced by =.  
   Saves some work unifying.  
   (Contributed by Patrick Brosnan, 9-Jun-2021.) $)
e-congrd   $p |- implies phi
                          iff = s0 t0
                              = s1 t1 $=
  ( binpred_equals eq-congrd ) ABCDHEFGI $.
$}



${
eq-congr-rt-d.1 $e |- implies phi = t0 t1 $.
$( Right deduction from eq-congr. 
   (Contributed by Patrick Brosnan, 18-May-2021.) $)
eq-congr-rt-d   $p |- implies phi 
                           iff binpred s t0
                               binpred s t1 $=
  ( binpred_equals wff_atom eq-refl a1i eq-congrd ) AABCDEAAGHEAIJFK $.
$}

${
eq-congr-lf-d.1 $e |- implies phi = s0 s1 $.
$( Left deduction from eq-congr. 
   (Contributed by Patrick Brosnan, 20-May-2021.) $)
eq-congr-lf-d   $p |- implies phi 
                              iff binpred s0 t  
                                  binpred s1 t $=
  ( binpred_equals wff_atom eq-refl a1i eq-congrd ) BCAADEFAAGHEAIJK $. 
$}

pa_ax2iffl $p |- iff = x     y 
                     = S x S y $=
  ( tvar binpred_equals wff_atom tsucc eq-suc pa_ax2 iff-ded ) ACZBCZDEJFKFDEJK
  GABHI $. 

${
$d x y $.
$d y t $.
pa_ax2tl $p |- iff = S x S t
                   = x t $=
  ( vary quant_all logbinopimplies logbinopiff tvar binpred_equals wff_logbinop
  wff_atom wff_quant pa_ax2iffl iffcomd a1i gen eq-suc eq-congr-rt-d iff-congrd
  tsucc id all_elim3 ax-mp ) CDEFBGZCGZHJZUCSZUDSZHJZIZUDAHJZIZKFUCAHJZUFASZHJZ
  IZCUKUIUJUEUHBCLMNOACUIUOUJUHUNUEULUFUGUMHUJUDAPQUCUDAHUJUJTQRUAUB $.
$}

${
$d x s $.
$d x t $.

pa_ax2t $p |- iff = S s S t 
                  =   s   t $=
  ( varx quant_all logbinopimplies logbinopiff tvar binpred_equals wff_logbinop
  wff_atom wff_quant pa_ax2tl a1i gen eq-suc eq-congr-lf-d iff-congrd all_elim3
  tsucc id ax-mp ) CDEFCGZBHJZUBSZBSZHJZIZUBAHJZIZKFABHJZASZUEHJZIZCUIUGUHBCLMN
  ACUGUMUHUFULUCUJUEUDUKHUHUBAOPBUBAHUHUHTPQRUA $.
$}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                     ELEMENTARY ARITHMETIC 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

   (Contributed by Patrick Brosnan, 12-Apr-2021.) 

$)


${
$d x s $.
$( Term version of pa_ax3.  Mendelson Lemma 3.1 S5' 
   (Contributed by Patrick Brosnan, 21-May-2021.) $)
pa_ax3t   $p |- = s + s 0 $=
  ( varx quant_all logbinopimplies tzero binop_plus binpred_equals wff_logbinop
  tvar tbinop wff_atom wff_quant pa_ax3 a1i gen eq-refl eq-binop simpand ax-mp
  id comd eq-congrd all_elim3 ) BCDBIZUDEFJZGKZUDAGKZHZLAAEFJZGKZBUHUFUGBMNOABU
  FUJUDAUEUIGUGUGTEEGKZDUEUIGKZUGHEPUGUKULUGUKULUDAEEFQRUASUBUCS $.
$}


${
eqbinoprtd.1 $e |- implies phi = t0 t1 $.
$( Deduction to shorten some uses of eq-binop. 
   (Contributed by Patrick Brosnan, 24-May-2021.) $)
eqbinoprtd $p |- implies phi = binop s t0 binop s t1 $=
  ( binpred_equals wff_atom tbinop logbinopimplies wff_logbinop eq-refl simpand
  eq-binop ax-mp syl ) EBCGHZABDIACDIGHZFAAGHZJRQKALSQRAABCDNMOP $.
$}


${
eqbinoplfd.1 $e |- implies phi = s0 s1 $.
$( Version of eqbinoprtd for changing the left summand. 
   (Contributed by Patrick Brosnan, 24-May-2021.) $)
eqbinoplfd   $p |- implies phi = binop s0 t
                                 binop s1 t $=
  ( binpred_equals wff_atom tbinop logbinopimplies wff_logbinop eq-refl simpand
  eq-binop comd ax-mp syl ) EBCGHZBADICADIGHZFAAGHZJSRKALRTSRTSBCAADNMOPQ $.
$}


${
bnpd.1 $e |- implies phi = s0 s1 $.
bnpd.2 $e |- implies phi = t0 t1 $.
$( eqbinop lf and rt together. 
   (Contributed by Patrick Brosnan, 25-May-2021.) $)
bnpd   $p |- implies phi = binop s0 t0 binop s1 t1 $=
  ( logbinopand binpred_equals wff_atom wff_logbinop tbinop anddant eq-binop
  syl ) FICDJKZABJKZLACEMBDEMJKFRQGHNABCDEOP $.
$}

${
eqplusd.1 $e |- implies phi = s0 s1 $.
eqplusd.2 $e |- implies phi = t0 t1 $.
$( Version of bnpd with + instead of binop.
   Hopefully will help in unifying.  
   (Contributed by Patrick Brosnan, 9-Jun-2021.) $)
eqplusd   $p |- implies phi = + s0 t0 + s1 t1 $=
  ( binop_plus bnpd ) ABCDHEFGI $.
$}

${
eqtimesd.1 $e |- implies phi = s0 s1 $.
eqtimesd.2 $e |- implies phi = t0 t1 $.
$( Version of bnpd with * instead of binop.  
   (Contributed by Patrick Brosnan, 9-Jun-2021.) $)
eqtimesd   $p |- implies phi = * s0 t0 * s1 t1 $=
  ( binop_times bnpd ) ABCDHEFGI $.
$}


${
bnpi.1 $e |- = s0 s1 $.
bnpi.2 $e |- = t0 t1 $.
$( Inference form of bnpd.  
   (Contributed by Patrick Brosnan, 29-May-2021.) $)
bnpi   $p |- = binop s0 t0
               binop s1 t1 $=
  ( tzero binpred_equals wff_atom tbinop eq-refl a1i bnpd ax-mp ) HHIJZACEKBDEK
  IJHLABCDEPABIJPFMCDIJPGMNO $.

$}


${
eqplusi.1 $e |-  = s0 s1 $.
eqplusi.2 $e |-  = t0 t1 $.
$( Version of bnpd with + instead of binop.
   Hopefully will help in unifying.  
   (Contributed by Patrick Brosnan, 9-Jun-2021.) $)
eqplusi   $p |-  = + s0 t0 + s1 t1 $=
  ( binop_plus bnpi ) ABCDGEFH $.
$}

${
eqtimesi.1 $e |-  = s0 s1 $.
eqtimesi.2 $e |-  = t0 t1 $.
$(  Version of bnpi with * instead of binop.  
   (Contributed by Patrick Brosnan, 9-Jun-2021.) $)
eqtimesi   $p |-  = * s0 t0 * s1 t1 $=
  ( binop_times bnpi ) ABCDGEFH $.
$}



${
$d x y $.
$d y t $.
$( Lemma for term version of pa_ax4. 
   (Contributed by Patrick Brosnan, 24-May-2021.) $)
pa_ax4tlem $p |- = S + x t
                   + x S t $=
  ( vary quant_all logbinopimplies binop_plus tsucc binpred_equals wff_logbinop
  tvar tbinop wff_atom wff_quant pa_ax4 a1i gen id eqbinoprtd eq-suc syl ax-mp
  eq-congrd all_elim3 ) CDEBJZCJZFKZGZUDUEGZFKZHLZUEAHLZIZMUDAFKZGZUDAGZFKZHLZC
  ULUJUKBCNOPACUJUQUGUNUIUPHUKUKUFUMHLUGUNHLUDUEAFUKUKQRUFUMSTUDUHUOFUKUEASRUBU
  CUA $.
$}

$(

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                 ANOTHER UNIVERSAL QUANTIFIER TRICK 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

Here's the idea of the theorem v2td (which stands for "variable
to term").  If you look up further in the file you see the text

  Then [after adding finitely many additional correct axioms whose
  choice does not depend on phi] we can prove in Metamath:

  |- iff
       forall x implies
          = x t
          phi
      phi[t/x]

in Solovay's comments.   In other words, for the purposes of this
file, we could (or maybe should) take it as the definition of proper
substitution that phi[t/x] is the same thing as 
     
       forall x (x = t implies phi) 

What this means is that if we have  another wff psi which we can
prove to be just phi with t substituted in for x and if we know that
forall x phi holds, then we ought to know that psi always holds as 
well. In other words, we should be able to deduce psi.

$)


${
$d x chi $.
$d x t $.
v2td.1 $e  |- phi $.
v2td.2 $e  |- implies = x t 
               iff phi chi $.
$( Changing variables to terms. Would have been useful
for the proof of pa_ax1-4. 
   (Contributed by Patrick Brosnan, 24-May-2021.) $)
v2td   $p  |- chi $=
  ( quant_all logbinopimplies tvar binpred_equals wff_atom wff_logbinop a1i gen
  wff_quant all_elim3 ax-mp ) BGHCBIAJKZLZODBSCREMNABCDFPQ $.
$}


${
$d x tau $.
$d x s $.
$d y chi $.
$d y t $.
v22td.1 $e |- phi $.
v22td.2 $e |- implies = y t iff phi chi $.
v22td.3 $e |- implies = x s iff chi tau $.
$( Version of v2td with two substitutions. 
   (Contributed by Patrick Brosnan, 24-May-2021.) $)
v22td   $p |- tau $=
  ( v2td ) ACFGBDEFHIKJK $.
$}



$(

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                 BACK TO ARITHMETIC
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

$)



${
$d x t $.
$d x s $.
$( Term form of pa_ax4. 
   (Contributed by Patrick Brosnan, 24-May-2021.) $)
pa_ax4t $p |- = S + s t 
                + s S t $=
  ( varx tvar binop_plus tsucc binpred_equals wff_atom pa_ax4tlem id eqbinoplfd
  tbinop eq-suc syl eq-congrd v2td ) ACCDZBELZFZQBFZELZGHABELZFZATELZGHBCISUCUA
  UDGQAGHZUERUBGHSUCGHBQAEUEUEJZKRUBMNTQAEUEUFKOP $.
$}


${
$d x t $.
$( Term form of pa_ax5. 
   (Contributed by Patrick Brosnan, 24-May-2021.) $)
pa_ax5t   $p |- = 0 * t 0 $=
  ( varx tzero binop_times tbinop binpred_equals wff_atom pa_ax5 eq-refl a1i id
  tvar eqbinoplfd eq-congrd v2td ) ABCBLZCDEZFGCACDEZFGBHCCQRFPAFGZCCFGSCIJCPAD
  SSKMNO $. 
$}


${
$d x s $.
$d x t $.
$d y t $. 
$d x y $.

$( Term form of pa_ax6. 
   (Contributed by Patrick Brosnan, 25-May-2021.) $)
pa_ax6t  $p |- = + * s t s 
                   * s S t $=
  ( varx vary tvar binop_times tbinop binop_plus binpred_equals wff_atom pa_ax6
  tsucc id eqbinoprtd eq-refl a1i bnpd eq-suc eq-congrd eqbinoplfd v22td ) ABCD
  CEZDEZFGZUBHGZUBUCLZFGZIJUBBFGZUBHGZUBBLZFGZIJABFGZAHGZAUJFGZIJCDKUEUIUGUKIUC
  BIJZUDUHUBUBHUOUBUCBFUOUOMNUBUBIJUOUBOPQUBUFUJFUOUCBRNSUIUMUKUNIUBAIJZUHULUBA
  HUPBUBAFUPUPMZTUQQUJUBAFUPUQTSUA $.
$}


${
eq-transd.1 $e |- implies phi = s t $.
eq-transd.2 $e |- implies phi = t u $.
$( Deduction form of eq-trans. 
   (Contributed by Patrick Brosnan, 26-May-2021.) $)
eq-transd   $p |- implies phi = s u $=
  ( logbinopand binpred_equals wff_atom wff_logbinop anddant eq-trans syl ) DGB
  CHIZABHIZJACHIDONEFKABCLM $.
$}

${
eq-transi.1 $e |- = s t $.
eq-transi.2 $e |- = t u $.
$( Inference from eq-trans. 
   (Contributed by Patrick Brosnan, 28-May-2021.) $)
eq-transi   $p |- = s u $=
  ( tzero binpred_equals wff_atom eq-refl a1i eq-transd ax-mp ) FFGHZACGHFIABCM
  ABGHMDJBCGHMEJKL $.
$}

${
eq-transdi.1 $e |- implies phi = s t $.
eq-transdi.2 $e |- = t u $.
$( Deduction and then inference for eq-trans. 
   (Contributed by Patrick Brosnan, 29-May-2021.) $)
eq-transdi   $p |- implies phi = s u $=
  ( binpred_equals wff_atom a1i eq-transd ) ABCDEBCGHDFIJ $.
$}

${
eq-transid.1 $e |- = s t $.
eq-transid.2 $e |- implies phi = t u $.
$( Inference and then deduction for eq-trans. 
   (Contributed by Patrick Brosnan, 29-May-2021.) $)
eq-transid   $p |- implies phi = s u $=
  ( binpred_equals wff_atom a1i eq-transd ) ABCDABGHDEIFJ $.
$}


${
eq-sucd.1 $e |- implies phi = t u $.
$( Deduction for eq-suc. 
   (Contributed by Patrick Brosnan, 28-May-2021.) $)
eq-sucd   $p |- implies phi = S t S u $=
  ( binpred_equals wff_atom tsucc eq-suc syl ) CABEFAGBGEFDABHI $. 
$}

${
eq-suci.1  $e |- = t u $.
$( Inference for eq-suc 
   (Contributed by Patrick Brosnan, 28-May-2021.) $)
eq-suci     $p |- = S t S u $=
  ( binpred_equals wff_atom tsucc eq-suc ax-mp ) ABDEAFBFDECABGH $.
$}




$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                     INDUCTION 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

Here we attempt to use the (rather complicated) induction axiom.
The goal is to be able to prove things without messing around 
too much with quantifiers.
The theorem that lets us do this is "nindd" stated below.
The idea and the name for the theorem was stolen from set.mm.
But it has to be modified slightly to work in peano.mm. 
Essentially, subsets have to be changed into terms.

The way nindd works in practice, to prove a statement (usually
about terms) by induction, you have to prove three things

 1) the base case
 2) the inductive step
 3) a substitution rule saying that if y = t 
    then the statment with the variable y replaced 
    by t everywhere is equivalent to the statement y.

If the statement to be proved is a statement without quantifiers,
then there are no quantifiers needed in the 6 hypotheses (or goals)
of nindd.

Why so many goals?  It helps to give a concrete example.  
Suppose we want to prove addcom
 
 addcom  |- = + s t 
              + t s 

by induction on t.  Because of the way induction is formulated,
we need to replace t first with a variable, say y, so we can 
apply quantifiers to it. So we wind up having to deal with the 
statement you get when you replace t with y in addcom, namely,

  addcomy |- = + s y 
               + y s.

But note that Solovay's induction axiom has two variables appearing
in it: x and y.  So we need another statement with t replaced by x.
Then to deal with the base case, we need a statement with t replaced
by 0.  And to deal efficiently with induction we need a statement 
with t replace by S y.

So if phi denotes the statement addcomy, then we get 4 statements:
with S y, with x, with t and with 0 that need to be proved equivalent
to addcomy under the appropriate substitution and we need to prove
the base case and induction.  So that makes up the 6 hypotheses of
nindd.

(Commentary contributed by Patrick Brosnan, 27-May-2021.)

$)

${
$d phi x $.
$d x y $.
indi.1 $e |- implies = y 0 phi $.
indi.2 $e |- implies forall y implies = y x phi 
                     forall y implies = y S x phi $.
$( An easy, but probably not too useful, deduction form of induction. 
   Took a long time for improve to deal with the f statements: 
   probably due to the length of the induction axiom.
   Actually needed to help it out manually in the end.
   (Contributed by Patrick Brosnan, 27-May-2021.) $)
indi   $p |- forall x forall y implies = y x phi $=
  ( logbinopand logbinopimplies tvar tsucc binpred_equals wff_atom wff_logbinop
  quant_all wff_quant tzero gen andd induction ax-mp ) FAMGBMGCBHZAHZIJKLNBMGCT
  UAJKLNZLZNZBMGCTOJKLZNZLAMUBNUFUDBUEDPAUCEPQABCRS $.
$}



${
$d y x $.
$d y t $.
$d y psi $.
$d y chi $.
$d y theta $.
$d y tau $.
$d x phi $.
nindd.1 $e |- implies = y 0 iff phi psi $.
nindd.2 $e |- implies = y x iff phi chi $.
nindd.3 $e |- implies = y S x iff phi theta $.
nindd.4 $e |- implies = y t  iff phi tau $.
nindd.5 $e |- psi $.
nindd.6 $e |- implies chi theta $. 
$( The theorem nindd copied, with hopefully suitable modifications, from set.mm. 
   Hopefully more useful than indd because it doesn't have quantifiers in statement. 
   (Contributed by Patrick Brosnan, 27-May-2021.) $)
nindlem1 $p |- implies forall y implies = y x phi
                       forall y implies = y S x phi $=
  ( quant_all logbinopimplies tvar binpred_equals wff_logbinop syl wff_atom bi2
  wff_quant tsucc all_elim3 logbinopiff comd alpha_2 ) COPDCQZBQZRUASUCZHCOPDUI
  UJUDRUAZSZUCUKFHUJCDFJUENTCHUMULHDULUFHDSPDHSKDHUBTUGUHT $.

nindd   $p |- tau $=
  ( quant_all logbinopimplies tvar binpred_equals wff_atom wff_quant tzero indi
  wff_logbinop indlem nindlem1 substl alpha1i iffmp all_elim subswl vswpmp
  ax-mp ) ACDGBOPFBQZCQZRSUCTZDBOFTZUOBOCOPDUNUMRSUCTZTUPBCDUNUARSDEIMUDABCDEFG
  HIJKLMNUEUBBOUQFUMCDFJUFUGUHUNBFUIULUNBFDUNUMDFJUJUFUHLUK $.
$}


$(

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                     FIRST INDUCTION THEOREMS 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

Here we start proving basic results in peano arithmetics using the 
induction theorem.  The first things to deal with are various versions
of the Peano axioms with the order of operations switched.  
Then we deal with associativity and commutativity of addition.

$)

$( We start with some lemmas to help with the first induction theorem: pa_ax3c. $)

pa_ax3cl1 $p |- = 0 + 0 0 $=
  ( tzero pa_ax3t ) AB $.

pa_ax3cl2 $p |- implies = t + 0 t 
                        = S t + 0 S t $=
  ( tsucc tzero binop_plus tbinop binpred_equals wff_atom pa_ax4t a1i eq-transd
  eq-suc ) ABZCADEZBZCLDEZAMFGZAMKNOFGPCAHIJ $.

pa_ax3cl3 $p |- implies = s t iff = s + 0 s
                                  = t + 0 t $=
  ( tzero binop_plus tbinop binpred_equals wff_atom eq-refl a1i bnpd eq-congrd
  id ) ABCADECBDEFABFGZMLZCCABDMCCFGMCHINJK $.

${
$d x y t $.
$( First theorem to be proved using induction. 
   (Contributed by Patrick Brosnan, 28-May-2021.) $)
pa_ax3c  $p |- = t + 0 t $=
  ( varx vary tvar tzero binop_plus binpred_equals wff_atom pa_ax3cl3 pa_ax3cl1
  tbinop tsucc pa_ax3cl2 nindd ) ABCCDZEOFKGHEEEFKGHBDZEPFKGHAEAFKGHPLZEQFKGHOE
  IOPIOQIOAIJPMN $.
$}

$( Lemmas for pa_ax4c: pa_ax4 with roles of x and y switched. 
   (Contributed by Patrick Brosnan, 28-May-2021.) $)

pa_ax4cl1 $p |- = S + t 0 + S t 0 $=
  ( tzero binop_plus tbinop tsucc binpred_equals wff_atom eq-sym-d eq-suc ax-mp
  pa_ax3t eq-transi ) ABCDZEZAEZOBCDMAFGNOFGAMAKHMAIJOKL $.

pa_ax4cl2 $p |- implies = S + t u + S t u 
                        = S + t S u + S t S u $=
  ( tsucc binop_plus tbinop binpred_equals wff_atom pa_ax4t eq-sym-d a1i eq-suc
  eq-suci eq-transd ) ABCZDEZCZACZBDEZCZQNDEZABDECZRFGZPUACZSUBPUCFGUBUCPUAOABH
  LIJUARKMSTFGUBQBHJM $.

pa_ax4cl3 $p |- implies = s u iff = S + t s + S t s  
                                  = S + t u + S t u $=
  ( binop_plus tbinop tsucc binpred_equals wff_atom eq-refl a1i id bnpd eq-sucd
  eq-congrd ) BADEZFBCDEZFBFZADEQCDEGACGHZOPRBBACDRBBGHRBIJRKZLMQQACDRQQGHRQIJS
  LN $.

${
$d x y t $.
$d x y u $.
$( pa_ax4t with roles of s and t switched. 
   (Contributed by Patrick Brosnan, 29-May-2021.) $)
pa_ax4c $p |- = S + t u + S t u $=
  ( varx vary tvar binop_plus tsucc binpred_equals wff_atom pa_ax4cl3 pa_ax4cl1
  tbinop tzero pa_ax4cl2 nindd ) BCDADEZFLGAGZPFLHIAMFLGQMFLHIACEZFLGQRFLHIABFL
  GQBFLHIARGZFLGQSFLHIPAMJPARJPASJPABJAKARNO $.
$}


ngeq $p |- implies 
                 = a b
                 = + a c
                   + b c $=
  ( binop_plus binpred_equals wff_atom id eq-refl a1i bnpd ) ABCCDABEFZKGCCEFKC
  HIJ $.
              

$( Something from Natural Numbers Game.  Contributed bb Patrick Brosnan. 
   (Contributed by Patrick Brosnan, 29-May-2021.) $)
nn26l0 $p |- = + a b 
               + + a b 0 $=
  ( binop_plus tbinop pa_ax3t ) ABCDE $.



nn26l1 $p |- = + + a b 0 
               + a + b 0 $=
  ( binop_plus tbinop tzero pa_ax3t eq-sym-d eq-refl bnpi eq-transi ) ABCDZECDZ
  KABECDZCDKLKFGAABMCAHBFIJ $.  

addass_base $p |- = + + a b 0 
                   + a + b 0 $=
  ( nn26l1 ) ABC $.

addass_ind  $p |- implies = + + a b c 
                           + a + b c
                         = + + a b S c 
                           + a + b S c $=
  ( binop_plus tbinop tsucc binpred_equals wff_atom pa_ax4t eq-sym-d a1i eq-suc
  eq-transd eq-refl bnpi eq-transi ) ABDEZCFZDEZABCDEZDEZFZABRDEZDEZQCDEZUAGHZS
  UEFZUBUFSUGGHUFUGSQCIJKUEUALMUBUDGHUFUBATFZDEUDATIAAUHUCDANBCIOPKM $.

addass_sub  $p |- implies = c d 
                          iff = + + a b c
                                + a + b c 
                              = + + a b d
                                + a + b d $=
  ( binop_plus tbinop binpred_equals wff_atom id eqbinoprtd syl eq-congrd ) ABE
  FZCEFMDEFABCEFZEFZABDEFZEFZGCDGHZMCDERRIZJRNPGHZOQGHBCDERSJANPETTIJKL $.

${
$d x y a $.
$d x y b $.
$d x y c $. 
$( Associativity of addition. $)

addass $p |- = + + a b c 
               + a + b c $=
  ( varx vary binop_plus tbinop binpred_equals wff_atom tzero tsucc addass_base
  tvar addass_sub addass_ind nindd ) CDEABFGZEMZFGABRFGFGHIQJFGABJFGFGHIQDMZFGA
  BSFGFGHIQCFGABCFGFGHIQSKZFGABTFGFGHIABRJNABRSNABRTNABRCNABLABSOP $. 
$}

$( Associativity for addition again, but with the numbering taken from the 
   Lean Natural Numbers Game Exercise. $)
nn26   $p |- = + + a b c 
               + a + b c $=
  ( addass ) ABCD $.  

addcom_base   $p |- = + a 0 + 0 a $=
  ( tzero binop_plus tbinop pa_ax3t eq-sym-d pa_ax3c eq-transi ) ABCDZABACDAIAE
  FAGH $.

addcom_ind    $p |- implies = + a b + b a
                            = + a S b + S b a $=
  ( tsucc binop_plus tbinop binpred_equals wff_atom pa_ax4t eq-sym-d eq-transid
  eq-suc pa_ax4c eq-transdi ) ABCZDEZBADEZCZNADEABDEZPFGZORCZQSTOABHIRPKJBALM
  $.

binopcom_sub  $p |- implies = b c  
                             iff  = binop a b binop b a 
                                 = binop a c binop c a $=
  ( tbinop binpred_equals wff_atom eq-refl a1i id bnpd eq-congrd ) BCAEBDAECBAE
  DBAEFCDFGZBBCDAMBBFGMBHIZMJZKCDBBAMONKL $.

addcom_sub    $p |- implies = b c  
                            iff  = + a b + b a 
                                 = + a c + c a $=
  ( binop_plus binopcom_sub ) DABCE $.

${
$d x y a $.
$d x y b $. 
$( Commutativity of addition.  $)
addcom  $p |- = + a b 
                + b a $=
  ( varx vary binop_plus tbinop binpred_equals wff_atom tzero tsucc addcom_base
  tvar addcom_sub addcom_ind nindd ) BCDADLZEFPAEFGHAIEFIAEFGHACLZEFQAEFGHABEFB
  AEFGHAQJZEFRAEFGHAPIMAPQMAPRMAPBMAKAQNO $. 
$}

$(

-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.

          CONVENIENCE THEOREMS
   
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.

What follows is an unfortunately very large number
of the deductions, inferences and theorems that is
supposed to help in proving equalities with the 
proof assistant in a more or less automatic
way.  Ideally, the goal would be to be able to prove 
equalities in the metamath proof assistant without
planning anything out beforehand. 
The idea is to keep proving statements of the
form 

A = B

or 

phi implies A = B

at all times in the proof.

The main problem with this approach seems to be 
the number of theorems, deductions and inferences
needed to really make it feel "automatic."  
They have the tendency to increase exponentially:
If for every result you need a theorem, deduction
and an inference, it multiplies the number of 
propositions you need by 3.  But then you might need
a statement for "+" and one for "*" and that multiplies
it by 2.  The upshot is that this sort of thing
needs to be planned out very well to be effective.

(Commentary contributed by Patrick Brosnan, 10-Jun-2021.)

$)

${
eqsymded.1 $e |- implies phi = a b $.
$( Deduction form of the (badly named theorem) eq-sym-d. 
   (Contributed by Patrick Brosnan, 30-May-2021.) $)
eqsymded   $p |- implies phi = b a $=
  ( binpred_equals wff_atom eq-sym syl ) ABCEFCBEFDBCGH $.
$}

${
eqax4d.1  $e |- implies phi = S + a b c $.
$( Deduction use of pa_ax4. 
   (Contributed by Patrick Brosnan, 30-May-2021.) $)
eqax4d    $p |- implies phi = + a S b c $=
  ( tsucc binop_plus tbinop binpred_equals wff_atom pa_ax4t eq-sym-d eq-transd
  a1i ) BCFGHZBCGHFZDAOPIJAPOBCKLNEM $.
$}


${
eqax4i.1  $e |- = S + a b c $.
$( Deduction use of pa_ax4. 
   (Contributed by Patrick Brosnan, 30-May-2021.) $)
eqax4i    $p |- = + a S b c $=
  ( tzero binpred_equals wff_atom tsucc binop_plus tbinop eq-refl eqax4d ax-mp
  a1i ) EEFGZABHIJCFGEKOABCABIJHCFGODNLM $.
$}


${
eqax4rd.1  $e |- implies phi = + a S b c $.
$( Deduction use of pa_ax4 reversed. 
   (Contributed by Patrick Brosnan, 30-May-2021.) $)
eqax4rd    $p |- implies phi = S + a b c $=
  ( binop_plus tbinop tsucc binpred_equals wff_atom eq-refl eqax4i eq-sym-d a1i
  eq-transd ) BCFGHZBCHFGZDAPQIJAQPBCPPKLMNEO $.
$}

${
eqax4ri.1  $e |- = + a S b c $.
$( Deduction use of pa_ax4 reversed. 
   (Contributed by Patrick Brosnan, 30-May-2021.) $)
eqax4ri    $p |- = S + a b c $=
  ( tzero binpred_equals wff_atom binop_plus tbinop tsucc eq-refl eqax4rd ax-mp
  a1i ) EEFGZABHIJCFGEKOABCABJHICFGODNLM $.
$}


${
eqax4cd.1  $e |- implies phi = S + a b c $.
$( Deduction use of pa_ax4. 
   (Contributed by Patrick Brosnan, 30-May-2021.) $)
eqax4cd    $p |- implies phi = + S a b c $=
  ( tsucc binop_plus tbinop binpred_equals wff_atom pa_ax4c eq-sym-d eq-transd
  a1i ) BFCGHZBCGHFZDAOPIJAPOBCKLNEM $.
$}

${
eqax4crd.1  $e |- implies phi = + S a b c $.
$( Deduction use of pa_ax4. 
   (Contributed by Patrick Brosnan, 30-May-2021.) $)
eqax4crd    $p |- implies phi = S + a b c $=
  ( binop_plus tbinop tsucc binpred_equals wff_atom pa_ax4c a1i eq-transd ) BCF
  GHZBHCFGZDANOIJABCKLEM $.
$}

${
eqaddcomd.1   $e |- implies phi = + a b c $.
$( Deduction use of addcom in equations. 
   (Contributed by Patrick Brosnan, 30-May-2021.) $)
eqaddcomd     $p |- implies phi = + b a c $=
  ( binop_plus tbinop addcom eq-transid ) CBFGBCFGDACBHEI $.
$}

${
eqaddcomi.1   $e |-  = + a b c $.
$( Deduction use of addcom in equations. 
   (Contributed by Patrick Brosnan, 30-May-2021.) $)
eqaddcomi     $p |- = + b a c $=
  ( binop_plus tbinop addcom eq-transi ) BAEFABEFCBAGDH $.
$}


${
eqaddassd.1  $e |- implies phi = + + a b c d $.
$( Deduction use of addass in equations. 
   (Contributed by Patrick Brosnan, 30-May-2021.) $)
eqaddassd    $p |- implies phi = + a + b c d $=
  ( binop_plus tbinop addass eq-sym-d eq-transid ) BCDGHGHZBCGHDGHZEAMLBCDIJFK
  $.
$}

${
eqaddassi.1  $e |- = + + a b c d $.
$( Deduction use of addass in equations. 
   (Contributed by Patrick Brosnan, 30-May-2021.) $)
eqaddassi    $p |- = + a + b c d $=
  ( binop_plus tbinop addass eq-sym-d eq-transi ) ABCFGFGZABFGCFGZDLKABCHIEJ $.
$}


${
eqaddassrd.1  $e |- implies phi = + a + b c d $.
$( Deduction use in reverse. 
   (Contributed by Patrick Brosnan, 30-May-2021.) $)
eqaddassrd    $p |- implies phi = + + a b c d $=
  ( binop_plus tbinop addass eq-transid ) BCGHDGHBCDGHGHEABCDIFJ $.
$}

${
eqaddassri.1  $e |- = + a + b c d $.
$( Deduction use in reverse. 
   (Contributed by Patrick Brosnan, 30-May-2021.) $)
eqaddassri    $p |- = + + a b c d $=
  ( binop_plus tbinop addass eq-transi ) ABFGCFGABCFGFGDABCHEI $.
$}



${
eqax4ci.1  $e |- = S + a b c $.
$( Deduction use of pa_ax4. 
   (Contributed by Patrick Brosnan, 30-May-2021.) $)
eqax4ci    $p |- = + S a b c $=
  ( tzero binpred_equals wff_atom tsucc binop_plus tbinop eq-refl eqax4cd ax-mp
  a1i ) EEFGZAHBIJCFGEKOABCABIJHCFGODNLM $.
$}

${
eqax6ti.1 $e |- = + * a b a c $.
$( Inference for pa_ax6 in equations. 
   (Contributed by Patrick Brosnan, 31-May-2021.) $) 
eqax6ti   $p |- = * a S b c $=
  ( tsucc binop_times tbinop binop_plus pa_ax6t eq-sym-d eq-transi ) ABEFGZABFG
  AHGZCMLABIJDK $.
$}

${
eqax6td.1 $e |- implies phi = + * a b a c $.
$( Deduction for pa_ax6 in equations. 
   (Contributed by Patrick Brosnan, 31-May-2021.) $)
eqax6td   $p |- implies phi = * a S b c $=
  ( tsucc binop_times tbinop binop_plus pa_ax6t eq-sym-d eq-transid ) BCFGHZBCG
  HBIHZDANMBCJKEL $.
$}


${
eqax6rti.1 $e |- = * a S b c $.
$( Inference for pa_ax6 in equations. 
   (Contributed by Patrick Brosnan, 31-May-2021.) $) 
eqax6rti   $p |- = + * a b a c $=
  ( binop_times tbinop binop_plus tsucc pa_ax6t eq-transi ) ABEFAGFABHEFCABIDJ
  $.
$}

${
eqax6rtd.1 $e |- implies phi = * a S b c $.
$( Deduction for pa_ax6 in equations. 
   (Contributed by Patrick Brosnan, 31-May-2021.) $)
eqax6rtd   $p |- implies phi = + * a b a c $=
  ( binop_times tbinop binop_plus tsucc pa_ax6t eq-transid ) BCFGBHGBCIFGDABCJE
  K $.
$}


$(

-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.

           MORE (elementary) PEANO THEOREMS
   
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.


   (Contributed by Patrick Brosnan, 30-May-2021.) $)

pa_ax6c_base $p |- = + * a 0 0 * S a 0 $=
  ( tzero binop_times tbinop binop_plus pa_ax3t eq-sym-d pa_ax5t eq-transi
  tsucc ) ABCDZBEDZBAJZBCDLKBKLKFGBKAHGIMHI $.

pa_ax6c_ind  $p |- implies = + * a b b 
                             * S a b 
                           = + * a S b S b 
                             * S a S b $=
  ( tsucc binop_times tbinop binop_plus binpred_equals wff_atom pa_ax6t eq-refl
  eq-sym-d bnpi addass eq-transi eqax4i eqax4ci addcom eq-suci a1i eq-transd id
  bnpd ) ABCZDEZUCFEZACZBDEZUFFEZUFUCDEZABDEZBFEZUGGHZUEUKUFFEZUHULUEUMGHULUEUJ
  BUFFEZFEZUMUEUJUFBFEZFEZUOUEUJABFEZCZFEZUQUEUJAUCFEZFEZUTUEUJAFEZUCFEVBUDVCUC
  UCFVCUDABIKUCJLUJAUCMNUJUJVAUSFUJJZABUSUSJZOLNUQUTUJUJUPUSFVDABUSVEPLKNUJUJUP
  UNFVDABUNUNUSBAUSBAFEURBAQROKPLNUMUOUJBUFMKNSUKUGUFUFFULULUAUFUFGHULUFJSUBTUH
  UIGHULUFBIST $.
pa_ax6c_sub  $p |- implies = b c
                           iff = + * a b b
                                 * S a b
                               = + * a c c 
                                 * S a c $=
  ( binop_times tbinop binop_plus tsucc binpred_equals wff_atom a1i id eqtimesd
  eq-refl eqplusd e-congrd ) ABDEZBFEACDEZCFEAGZBDERCDEBCHIZPQBCSAABCSAAHISAMJS
  KZLTNRRBCSRRHISRMJTLO $.

${ 
$d x y a $.
$d x y b $.
pa_ax6c  $p |- = + * a b b * S a b $=
  ( varx vary binop_times tbinop binop_plus tsucc binpred_equals wff_atom tzero
  tvar pa_ax6c_sub pa_ax6c_base pa_ax6c_ind nindd ) BCDADLZEFQGFAHZQEFIJAKEFKGF
  RKEFIJACLZEFSGFRSEFIJABEFBGFRBEFIJASHZEFTGFRTEFIJAQKMAQSMAQTMAQBMANASOP $.  
$}

pa_ax5c_base $p |- = 0 * 0 0 $=
  ( tzero pa_ax5t ) AB $.

pa_ax5c_ind  $p |- implies = 0 * 0 a
                           = 0 * 0 S a  $=
  ( tzero binop_times tbinop binpred_equals wff_atom binop_plus pa_ax3t pa_ax6t
  tsucc id eq-transi eq-transdi ) BBACDZBAJCDZBNEFZPKNNBGDONHBAILM $.

pa_ax5c_sub  $p |- implies = a b iff = 0 * 0 a 
                                     = 0 * 0 b $=
  ( binop_times tbinop binpred_equals wff_atom eq-refl a1i id eqtimesd e-congrd
  tzero ) LLLACDLBCDABEFZLLEFMLGHZLLABMNMIJK $.

${
$d x y a $.
pa_ax5c  $p |- = 0 * 0 a $=
  ( varx vary tzero tvar binop_times tbinop binpred_equals wff_atom pa_ax5c_sub
  tsucc pa_ax5c_base pa_ax5c_ind nindd ) ABCDDCEZFGHIDDDFGHIDDBEZFGHIDDAFGHIDDP
  KZFGHIODJOPJOQJOAJLPMN $. 
$}

mulcom_base  $p |- = * a 0 
                     * 0 a $=
  ( tzero binop_times tbinop pa_ax5t eq-sym-d pa_ax5c eq-transi ) ABCDZBBACDBIA
  EFAGH $. 

mulcom_ind   $p |- implies = * a b
                             * b a 
                           = * a S b 
                             * S b a $=
  ( tsucc binop_times tbinop binop_plus binpred_equals wff_atom eq-sym-d a1i id
  pa_ax6t eq-refl eqplusd eq-transd pa_ax6c eq-transdi ) ABCZDEZBADEZAFEZRADEAB
  DEZTGHZSUBAFEZUAUCSUDGHUCUDSABLIJUBTAAUCUCKAAGHUCAMJNOBAPQ $.

mulcom_sub  $p |- implies = b c 
                          iff  = * a b 
                                 * b a 
                               = * a c
                                 * c a $=
  ( binop_times binopcom_sub ) DABCE $.

${
$d x y a $.
$d x y b $.
$( Commutativity of multiplication. 
   (Contributed by Patrick Brosnan, 10-Jun-2021.) $)
mulcom   $p |- = * a b 
                 * b a $=
  ( varx vary binop_times tbinop binpred_equals wff_atom tzero tsucc mulcom_sub
  tvar mulcom_base mulcom_ind nindd ) BCDADLZEFPAEFGHAIEFIAEFGHACLZEFQAEFGHABEF
  BAEFGHAQJZEFRAEFGHAPIKAPQKAPRKAPBKAMAQNO $.
$}

distr_base  $p |- = * a + b 0 
                    + * a b * a 0 $=
  ( tzero binop_plus tbinop eq-refl pa_ax3t eq-sym-d eqtimesi pa_ax5t eq-transi
  binop_times eqplusi ) ABCDEZLEABLEZOACLEZDEZAANBAFBNBGHIOOCDEQOGOOCPOFAJMKK
  $.

distr_ind  $p |- implies = * a + b c 
                          + * a b * a c 
                        = * a + b S c 
                          + * a b * a S c  $=
  ( tsucc binop_plus tbinop binop_times binpred_equals wff_atom eq-refl pa_ax4t
  eq-sym-d eqtimesi pa_ax6t eq-transi id a1i eqplusd eqsymded eqaddassd eqplusi
  eq-transid eq-transdi ) ABCDZEFZGFZABGFZACGFZAEFZEFZUGAUDGFZEFABCEFZGFZUGUHEF
  ZHIZUFUMAEFZUJUOUFAULDZGFZUPAAUEUQAJZUQUEBCKLMUPURAULNLOUOUJUPUOUGUHAUPUOUPUN
  AEFUMUNAAUOUOPAAHIUOUSQRSTSUBUGUGUIUKUGJACNUAUC $.

distr_sub $p |- implies = c d
                       iff = * a + b c 
                             + * a b * a c  
                           = * a + b d 
                             + * a b * a d $=
  ( binop_plus binop_times binpred_equals wff_atom eq-refl a1i eqplusd eqtimesd
  tbinop id e-congrd ) ABCEMZFMABDEMZFMABFMZACFMZEMRADFMZEMCDGHZAAPQUAAAGHUAAIJ
  ZBBCDUABBGHUABIJUANZKLRRSTUARRGHUARIJAACDUAUBUCLKO $. 

${
$d x y a $.
$d x y b $.
$d x y c $.
$( The distributive law. $)
distr  $p |- = * a + b c 
                   + * a b * a c $=
  ( varx vary binop_plus tbinop binop_times binpred_equals wff_atom tzero tsucc
  tvar distr_sub distr_base distr_ind nindd ) CDEABEMZFGHGABHGZARHGFGIJABKFGHGS
  AKHGFGIJABDMZFGHGSATHGFGIJABCFGHGSACHGFGIJABTLZFGHGSAUAHGFGIJABRKNABRTNABRUAN
  ABRCNABOABTPQ $.
$}

mulass_base  $p |- = * * a b 0 
                     * a * b 0 $=
  ( binop_times tbinop tzero pa_ax5t eq-sym-d eq-transi eq-refl eqtimesi ) ABCD
  ZECDZAECDZABECDZCDLEMELKFGAFHAAENAIBFJH $. 

mulass_ind  $p |- implies = * * a b c 
                            * a * b c 
                          = * * a b S c  
                            * a * b S c  $=
  ( binop_times tbinop binpred_equals wff_atom tsucc binop_plus eq-refl pa_ax6t
  eq-sym-d eqtimesi distr eq-transi id eqsymded a1i eqplusd eq-transid
  eq-transdi ) ABDEZCDEZABCDEZDEZFGZABCHZDEZDEZUBUGDEZUIUCUBIEZUJUFUIUEUBIEZUKU
  FUIAUDBIEZDEULAAUHUMAJUMUHBCKLMAUDBNOUEUCUBUBUFUFUCUEUFPQUBUBFGUFUBJRSTUBCKUA
  Q $. 
                            
mulass_sub  $p |- implies = c d iff = * * a b c 
                                      * a * b c 
                                    = * * a b d 
                                      * a * b d $=
  ( binop_times tbinop binpred_equals wff_atom eq-refl a1i eqtimesd eq-congrd
  id ) ABEFZCEFNDEFABCEFZEFABDEFZEFGCDGHZNNCDQNNGHQNIJQMZKAAOPQAAGHQAIJBBCDQBBG
  HQBIJRKKL $.   


${
$d x y a $.
$d x y b $.
$d x y c $.
$( Associativity for multiplication. 
   (Contributed by Patrick Brosnan, 11-Jun-2021.) $)
mulass  $p |- = * * a b c 
                * a * b c $=
  ( varx vary binop_times tbinop binpred_equals wff_atom tzero tsucc mulass_sub
  tvar mulass_base mulass_ind nindd ) CDEABFGZEMZFGABRFGFGHIQJFGABJFGFGHIQDMZFG
  ABSFGFGHIQCFGABCFGFGHIQSKZFGABTFGFGHIABRJLABRSLABRTLABRCLABNABSOP $. 
$}

addcanc_base  $p |- implies = + a 0 
                              + b 0 
                              = a b $=
  ( tzero binop_plus tbinop binpred_equals wff_atom pa_ax3t eq-transid eq-sym-d
  id eq-transdi ) ABCDEZBACDEZMFGZANMOAHOKIBMBHJL $.

$( 
Proof of addcanc_ind unified only after using
    improve 25 / depth 3
    with search_limit set to 10000000.
    Took about a minute.
$)
addcanc_ind  $p |- implies implies = + a c 
                                     + b c 
                                   = a b 
                            implies = + a S c 
                                      + b S c 
                                     = a b $=
  ( logbinopimplies binop_plus tbinop binpred_equals tsucc wff_logbinop pa_ax4t
  wff_atom id eq-transid eq-sym-d eq-transdi pa_ax2t ded-iff1 syl sylthm ax-mp
  ) DACEFZBCEFZGKZACHZEFZBUDEFZGKZIDDABGKZUGIDUHUCIIUGUAHZUBHZGKZUCUIUFUJUGUIUE
  UFUGACJUGLMUJUFBCJNOUKUCUAUBPQRUGUCUHST $.

${
addcanc_sublem.1 $e |- implies phi = s0 s1 $.
addcanc_sublem.2 $e |- implies phi = t0 t1 $. 
$( Lemma for addcanc_sub. 
   (Contributed by Patrick Brosnan, 13-Jun-2021.) $)
addcanc_sublem $p |- implies phi iff implies = s0 t0 psi
                                     implies = s1 t1 psi $=
  ( binpred_equals eq-congrd logbinopiff wff_logbinop prop-refl a1i prop-congrd
  wff_atom ) EACIPBDIPFFABCDIEGHJKFFLEFMNO $.
$}


addcanc_sub  $p |- implies = c d iff  implies = + a c 
                                                + b c 
                                               = a b
                                      implies = + a d 
                                                + b d 
                                               = a b $=
  ( binop_plus tbinop binpred_equals wff_atom eq-refl id eqplusd addcanc_sublem
  a1i ) ACEFADEFBCEFBDEFCDGHZABGHAACDNAAGHNAIMNJZKBBCDNBBGHNBIMOKL $.

${
$d x y a $.
$d x y b $.
$d x y c $.
$( Additive cancellation law. 
   (Contributed by Patrick Brosnan, 13-Jun-2021.) $)
addcanc  $p |- implies = + a c 
                         + b c 
                       = a b $=
  ( varx logbinopimplies binpred_equals wff_atom binop_plus tbinop wff_logbinop
  vary tvar tzero tsucc addcanc_sub addcanc_base addcanc_ind nindd ) CDKEABFGZA
  KLZHIBTHIFGJESAMHIBMHIFGJESADLZHIBUAHIFGJESACHIBCHIFGJESAUANZHIBUBHIFGJABTMOA
  BTUAOABTUBOABTCOABPABUAQR $.
$}


$(

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                    2b \/ ~2b (EXISTENTIAL QUANTIFIERS) 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

Before we do anything with inequalities, it seems we have to build up
some techniques for dealing with existential quantifiers.
This is what we're going to do here.

$)

${
exdfd.1 $e |- implies phi not forall x not psi $.
$( Deduction for def of existence. 
   (Contributed by Patrick Brosnan, 14-Jun-2021.) $)
exdfd   $p |- implies phi exists x psi $=
  ( quant_all wff_not wff_quant quant_ex exists_def ded-iff2 syl ) BAECFGFZAHCG
  ZDMLACIJK $.
$}


${
$d x chi $.
$d x t $.
exinsti.1 $e  |- implies = x t 
               iff phi chi $.
$( Way to instantiate a variable.  Copied basically from v2td. 
   (Contributed by Patrick Brosnan, 14-Jun-2021.) $)
exinsti   $p  |- implies chi exists x phi $=
  ( quant_all logbinopimplies wff_not tvar binpred_equals wff_atom wff_logbinop
  wff_quant ax3lemd all_elim3 pnotqd all_elim ax3rd syl exdfd ) BDCDBFGCHZBIAJK
  ZLMZHBFUAMZHUCDABUADHUBCDENOPUDUCABUAQRST $.
$}

${
$d x chi $.
$d x t $.
exinstic.1 $e  |- implies = x t 
               iff phi chi $.
exinstic.2 $e  |- chi $.
$( Corolllary of exinsti.  
   (Contributed by Patrick Brosnan, 14-Jun-2021.) $)
exinstic   $p  |- exists x phi $=
  ( quant_ex wff_quant exinsti ax-mp ) DBGCHFABCDEIJ $.
$}


${ 
$d chi x $.
   al2ex_hyp2 $e |- implies phi chi $.
$( Form of alpha_2 for existence. 
      (Contributed by Patrick Brosnan, 15-Jun-2021.) $)
   al2ex    $p |- implies exists x phi chi $=
     ( quant_ex wff_quant quant_all wff_not exists_def ax3rd alpha_2 notpqi syl
     ded-iff1 ) AEBFZAGBHZFZHZCORABINCQACHPBCDJKLM $.
$}

notsplem $p |- implies forall x not phi 
                    not exists x phi $=
  ( quant_ex wff_quant quant_all wff_not exists_def ded-iff1 pnotqd ) ACBDZAEBF
  DZJKFABGHI $.
${
notsp.1 $e |- not phi $.
$( Analogue of generalization governing specialization.  
   (Contributed by Patrick Brosnan, 3-May-2021.) $)
notsp   $p |- not exists x phi $=
  ( quant_all wff_not wff_quant quant_ex gen notsplem ax-mp ) ADBEZFAGBFEAKCHAB
  IJ $. 
$}



$(

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   LESS THAN               
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

In this subsection we use pa_ax7 to deal with less than.
It turns out that pa_ax7 is not correct.  So at the end of the section
we're going to derive a contradiction and prove that 0 = 1.
See "zerisone" for the proof of this, and then "anything" for the proof
of any wff.

The problem in pa_ax7 is that the variable z is allowed to be bundled with x 
and y.  So it's pretty easy to fix with two distinct variable conditions:
one to keep x and z distinct and another to keep y and z distinct.

$)

ltrsblli $p |- implies = c d iff = a + b c 
                                 = a + b d $=
  ( binop_plus tbinop binpred_equals wff_atom eq-refl a1i id eqplusd e-congrd )
  AABCEFBDEFCDGHZAAGHNAIJBBCDNBBGHNBIJNKLM $.

${
$d x a $.
$d x b $.
$d x t $.

ltrsblem.1 $e |- implies phi = a + b t $.
$( Substitution lemma for letransl. 
   (Contributed by Patrick Brosnan, 15-Jun-2021.) $)
ltrsblem $p |- implies phi exists x 
                                  = a + b x $=
  ( binop_plus binpred_equals wff_atom quant_ex tvar wff_quant ltrsblli exinsti
  tbinop syl ) CDEAGOHIZBJDEBKZGOHIZLFABSQDERAMNP $.
$}


${
$d x y z a $.
$d x y z b $.
$d x y z c $.

letransl $p |- implies and exists x = b + a x  
                       exists y = c + b y  
                    exists z = c + a z  $=
  ( quant_ex tvar binop_plus tbinop binpred_equals logbinopimplies wff_logbinop
  wff_atom wff_quant logbinopand andright andleft al2ex comd eq-refl a1i addass
  eqplusd eq-transdi eq-transd ltrsblem simpand simpandr ) AGEDAHZIJZKNZOZBGFEB
  HZIJZKNZOZCGFDCHIJKNOZUQUMURBUPLURUMMUMUPURAULLURUPMULUPURUJUNIJZCPUPULMZFDFU
  ODUSIJZUTULUPQUOUKUNIJVAUTEUKUNUNUTULUPRUNUNKNUTUNUAUBUDDUJUNUCUEUFUGUHSTSTUI
  $.
$}

pa_ax7tezl1 $p |- implies = d b iff = d 
                                      + a S c 
                                    = b
                                      + a S c $=
  ( tsucc binop_plus tbinop binpred_equals wff_atom id eq-refl a1i e-congrd ) D
  BACEFGZNDBHIZOJNNHIONKLM $.
pa_ax7tezl2 $p |- implies = d a iff = b
                                      + d S c
                                    = b
                                      + a S c $=
  ( tsucc binop_plus tbinop binpred_equals wff_atom eq-refl id eqplusd e-congrd
  a1i ) BBDCEZFGAOFGDAHIZBBHIPBJNDAOOPPKOOHIPOJNLM $.

${
$d y z $.
$d b z $.

pa_ax7l1 $p |- implies = y b iff exists z = y + x S z
                                 exists z = b + x S z 
                                    $=
  ( quant_ex tvar binpred_equals wff_atom binop_plus tbinop pa_ax7tezl1 alpha_1
  tsucc ) CEBFZDGHNAFZCFZMIJZGHDQGHODPNKL $.
$}

${
$d x z $.
$d a z $. 

pa_ax7l2 $p |- implies = x a iff 
                             exists z = b
                                        + x S z
                             exists z = b
                                        + a S z 
$=
  ( quant_ex tvar binpred_equals wff_atom binop_plus tbinop pa_ax7tezl2 alpha_1
  tsucc ) BEAFZCGHDNBFZMZIJGHDCPIJGHCDONKL $.
$} 

${
$d a x y z $.
$d b x y z $.
pa_ax7t  $p |- iff < a b exists z = b + a S z $=
  ( varx vary logbinopiff quant_ex binop_plus binpred_equals wff_atom wff_quant
  tvar tbinop binpred_less_than wff_logbinop eq-refl a1i eq-congrd iff-congrd
  id tsucc pa_ax7 pa_ax7l1 pa_ax7l2 v22td ) BCDEFAGELZDLZALUAZHMZIJKZUGUFNJZOFA
  GCUIIJKZUGCNJZOFAGCBUHHMIJKZBCNJZODEAUBUFCIJZUKUMUJULUGUGUFCNUPUGUGIJUPUGPQUP
  TRDEACUCSUGBIJZUMUOULUNUGBCCNUQUQTCCIJUQCPQRDABCUDSUE $.
$}

notsumcor $p |- not = b 
                      + a S b $=
  ( tsucc binop_plus tbinop binpred_equals wff_atom id eqsymded eqax4rd eqax4cd
  tzero pa_ax3c eq-transdi addcanc syl wff_not pa_ax1t a1i notcontrad ) BABCDEZ
  FGZLACZFGZUBUCLUBUCBDEZLBDEZFGUCLFGUEBUFUBUBABBUBABBUBBUAUBHIJKBMNUCLBOPIUDQU
  BARST $.

notsumexcor $p |- implies = y S x 
                          not exists y = y 
                                         + x S y $=
  ( quant_ex tvar binop_plus tbinop binpred_equals wff_atom wff_quant notsumcor
  tsucc wff_not notsp a1i ) BCBDZADZOKEFGHZILOPKGHBQPOJMN $.


$( 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                                LEMMAS FOR A CONTRADICTION 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

The original version of Axiom pa_ax7 from peano.mm had a small error:
it omitted the disjoint variables assumption.  In this section,
we're going to prove a few lemmas that will help to get a contradiction
from the original version of pa_ax7. Then, in the next section, we're going
assume the original version as an hypothesis and derive a contradiction.
First, we'll prove that 0 = 1, and then we'll use it to prove anything.

$)




${
$d a z $.
$( Just shows that a is less than its successor. $)
nlyest $p |- < a S a $=
  ( varz quant_ex tsucc tvar binop_plus tbinop binpred_equals binpred_less_than
  wff_atom wff_quant tzero eq-refl a1i eq-suc eqplusd e-congrd pa_ax3t pa_ax4t
  ax-mp eq-transi exinstic pa_ax7t ded-iff2 ) BCADZABEZDZFGZHJZKZAUEIJZLBUIUEAL
  DZFGZHJUEUEUHUMUFLHJZUEUEHJUNUEMNAAUGULUNAAHJUNAMNUFLOPQUEALFGZDZUMAUOHJUEUPH
  JARAUOOTALSUAUBUKUJBAUEUCUDT $. 
$}

$( Corollary of nlyest with a substitution. $)
nlyes $p |- implies = y S x 
                    < x y $=
  ( tvar binpred_equals wff_atom binpred_less_than eq-refl a1i eq-congrd nlyest
  tsucc id indlem ) BCZACZKZDEZONFEOPFEOONPFQOODEQOGHQLIOJM $.

pa_ax1_0 $p |- not = 0 S 0 $=
  ( tzero pa_ax1t ) AB $. 

exiy $p |- exists y = y S 0 $=
  ( tzero tsucc tvar binpred_equals wff_atom id eq-refl a1i e-congrd exinstic )
  BCZAADZLEFZLLEFZMLLLNNGONLHZIJPK $.

$( 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                                 CONTRADICTION  
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

As mentioned above, the original version of Axiom pa_ax7 from peano.mm had a small error:
it omitted the disjoint variables assumption.  Here we assume the original 
version of the axiom, pa_ax7orig below, and use it to get a contradiction.

Ideally, I would like to be able to confine pa_ax7orig to a frame using an $e statement,
and then derive a contradiction only in the frame.  However, I have not been able to make
this work.  Roughly speaking, the problem seems to be that the way variable substitions are handled in axioms
is different from the way they are handled in hypotheses. 

(Commentary added by Patrick Brosnan, 29-Jul-2021.)

$)

$( The original form of pa_ax7, with distinct variable hypotheses. $)
pa_ax7orig $a |- iff
               < x y
               exists z = y + x S z $.

$( An "incorrect" statement derivable using pa_ax7orig by substituting y and z for the same
variable. $)
nlcontr $p |- implies = y S x not < x y $=
  ( tsucc binpred_equals wff_atom binop_plus tbinop wff_quant binpred_less_than
  tvar quant_ex wff_not notsumexcor pa_ax7orig ded-iff1 ax3rd syl ) BJZAJZCDEBK
  RSRCFGDEHZLSRIEZLABMUATUATABBNOPQ $.

$( Another incorrect statement, but one where the conclusion is more obviously false. $)
nlfalse $p |- implies = y S x 
                      = 0 S 0 $=
  ( tsucc binpred_equals wff_atom binpred_less_than tzero nlyes nlcontr contrad
  tvar ) BKZAKZCDEMLFEGGCDEABHABIJ $.

${
$d x y $.
$d t x $.
$( Yet another incorrect statement.  Generalizes nlfalse by allying x to be a term. $)
nlfalsest $p |- implies = y S t 
                        = 0 S 0 $=
  ( varx logbinopimplies tzero binpred_equals tvar wff_logbinop nlfalse eq-refl
  tsucc wff_atom a1i eq-suc e-congrd logbinopiff prop-refl prop-congrd v2td ) A
  CDEEKFLZBGZCGZKZFLZHDTUAAKZFLZHCBIUBAFLZUDUFTTUAUAUCUEUGUAUAFLUGUAJMUBANOPTTH
  UGTQMRS $.
$}

$( Specialization of nlfalsest, where we substitute 0 for t. $)
nlspec $p |- implies = y S 0 
                     = 0 S 0 $=
  ( tzero nlfalsest ) BAC $.

$( First step at getting rid of variable y in nlspec, and then getting rid of hypothesis,
by quantifying over it. $)
exnlspec $p |- implies exists y = y S 0 
                       = 0 S 0 $=
  ( tvar tzero tsucc binpred_equals wff_atom nlfalsest al2ex ) AABCDZEFCIEFCAGH
  $. 

$( Prove that zerisone. Contradicts tzero obviously. $) 
zerisone $p |- = 0 S 0 $=
  ( vary quant_ex tvar tzero tsucc binpred_equals wff_atom wff_quant exiy ax-mp
  exnlspec ) ABACDEZFGHDLFGAIAKJ $.

$( Proves that any wff holds.  Something you can do (in classical logic) when you prove
a contradiction. $)
anything $p |- phi $=
  ( tzero tsucc binpred_equals wff_atom zerisone wff_not pa_ax1_0 contrad ax-mp
  id a1i ) BBCDEZAFMMAMKMGMHLIJ $.


