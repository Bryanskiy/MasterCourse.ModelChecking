------------------------------ MODULE main ------------------------------
EXTENDS Integers, TLC, Sequences

(*--algorithm SelfService

variables
    main = TRUE,
    pay = FALSE,
    block = FALSE,
    mloyal = FALSE,
    weight = FALSE,
    bag = FALSE,
    recalc = FALSE,
    recalc2 = FALSE,
    card = FALSE,
    stable = FALSE,

    rubles \in 0..20,
    cardBonuses \in 0..15,
    bagPrice \in 1..2,
    cheque = 0,

define
\*SAFETY
    PayAfterBonus == (pay => (mloyal /\ recalc))
    RemoveAfterAccess == (block => (recalc /\ recalc2))
    StableWeight == (weight /\ stable => recalc)
    BonusCard == (card => (mloyal /\ recalc))
\*LIVENESS
end define

fair process Register = "Register" begin
s8:
    await main = FALSE /\ bag = TRUE;
    cheque := cheque + bagPrice;
    bag := FALSE || main := TRUE;
    
s10:
    await main = FALSE /\ mloyal = TRUE;
    if card = TRUE then
        if cheque < cardBonuses then
            cardBonuses := cardBonuses - cheque;
            cheque := 0;
        else
            cheque := cheque - cardBonuses;
            cardBonuses := 0;
        end if;
    end if;
    goto s4;

s4:
    if cheque > rubles then
        s5: block := TRUE;
    else
        rubles := rubles - cheque;
        main := TRUE;
    end if;
end process

fair process Customer = "Customer" begin
s1:
    while(TRUE) do
        await main = TRUE;
        either
            \* put the product on the scale
            main := FALSE || weight := TRUE;
        or 
            \* buy bag
            main := FALSE || bag := TRUE;
        or 
            \* pay - loyalty program come first
            main := FALSE || mloyal := TRUE;
            either
                    card := TRUE
                or
                    card := FALSE
            end either;
        end either;
    end while
end process

end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES main, pay, block, mloyal, weight, bag, recalc, recalc2, card, 
          stable, rubles, cardBonuses, bagPrice, cheque, pc

(* define statement *)
PayAfterBonus == (pay => (mloyal /\ recalc))
RemoveAfterAccess == (block => (recalc /\ recalc2))
StableWeight == (weight /\ stable => recalc)
BonusCard == (card => (mloyal /\ recalc))


vars == << main, pay, block, mloyal, weight, bag, recalc, recalc2, card, 
           stable, rubles, cardBonuses, bagPrice, cheque, pc >>

ProcSet == {"Register"} \cup {"Customer"}

Init == (* Global variables *)
        /\ main = TRUE
        /\ pay = FALSE
        /\ block = FALSE
        /\ mloyal = FALSE
        /\ weight = FALSE
        /\ bag = FALSE
        /\ recalc = FALSE
        /\ recalc2 = FALSE
        /\ card = FALSE
        /\ stable = FALSE
        /\ rubles \in 0..20
        /\ cardBonuses \in 0..15
        /\ bagPrice \in 1..2
        /\ cheque = 0
        /\ pc = [self \in ProcSet |-> CASE self = "Register" -> "s8"
                                        [] self = "Customer" -> "s1"]

s8 == /\ pc["Register"] = "s8"
      /\ main = FALSE /\ bag = TRUE
      /\ cheque' = cheque + bagPrice
      /\ /\ bag' = FALSE
         /\ main' = TRUE
      /\ pc' = [pc EXCEPT !["Register"] = "s10"]
      /\ UNCHANGED << pay, block, mloyal, weight, recalc, recalc2, card, 
                      stable, rubles, cardBonuses, bagPrice >>

s10 == /\ pc["Register"] = "s10"
       /\ main = FALSE /\ mloyal = TRUE
       /\ IF card = TRUE
             THEN /\ IF cheque < cardBonuses
                        THEN /\ cardBonuses' = cardBonuses - cheque
                             /\ cheque' = 0
                        ELSE /\ cheque' = cheque - cardBonuses
                             /\ cardBonuses' = 0
             ELSE /\ TRUE
                  /\ UNCHANGED << cardBonuses, cheque >>
       /\ pc' = [pc EXCEPT !["Register"] = "s4"]
       /\ UNCHANGED << main, pay, block, mloyal, weight, bag, recalc, recalc2, 
                       card, stable, rubles, bagPrice >>

s4 == /\ pc["Register"] = "s4"
      /\ IF cheque > rubles
            THEN /\ pc' = [pc EXCEPT !["Register"] = "s5"]
                 /\ UNCHANGED << main, rubles >>
            ELSE /\ rubles' = rubles - cheque
                 /\ main' = TRUE
                 /\ pc' = [pc EXCEPT !["Register"] = "Done"]
      /\ UNCHANGED << pay, block, mloyal, weight, bag, recalc, recalc2, card, 
                      stable, cardBonuses, bagPrice, cheque >>

s5 == /\ pc["Register"] = "s5"
      /\ block' = TRUE
      /\ pc' = [pc EXCEPT !["Register"] = "Done"]
      /\ UNCHANGED << main, pay, mloyal, weight, bag, recalc, recalc2, card, 
                      stable, rubles, cardBonuses, bagPrice, cheque >>

Register == s8 \/ s10 \/ s4 \/ s5

s1 == /\ pc["Customer"] = "s1"
      /\ main = TRUE
      /\ \/ /\ /\ main' = FALSE
               /\ weight' = TRUE
            /\ UNCHANGED <<mloyal, bag, card>>
         \/ /\ /\ bag' = TRUE
               /\ main' = FALSE
            /\ UNCHANGED <<mloyal, weight, card>>
         \/ /\ /\ main' = FALSE
               /\ mloyal' = TRUE
            /\ \/ /\ card' = TRUE
               \/ /\ card' = FALSE
            /\ UNCHANGED <<weight, bag>>
      /\ pc' = [pc EXCEPT !["Customer"] = "s1"]
      /\ UNCHANGED << pay, block, recalc, recalc2, stable, rubles, cardBonuses, 
                      bagPrice, cheque >>

Customer == s1

Next == Register \/ Customer
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Register)
        /\ WF_vars(Customer)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
