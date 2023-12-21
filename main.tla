----------------------------- MODULE main ------------------------------
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
    productCost \in 1..5;
    cardBonuses \in 0..15,
    bagPrice \in 1..2,
    cheque = 0,

define
\*SAFETY
    PayAfterBonus == (mloyal ~> pay)
    RecalcAfterSuccsScale == (weight /\ stable ~> recalc)
    RemoveAfterAccess == (block ~> main)
    StableWeight == (weight /\ stable ~> recalc)
    BonusCard == (card ~> ~mloyal)
\*LIVENESS
    WillPay == (menu ~> <>pay)
    WillRecalc == (menu \/ stable \/ bag ~> recalc)
end define

fair process Register = "Register" begin
registerLoop:
    while(TRUE) do
        await recalc = TRUE;
        if main = FALSE /\ bag = TRUE then
            s8:
                cheque := cheque + bagPrice;
                bag := FALSE || main := TRUE || recalc := FALSE;
        elsif main = FALSE /\ mloyal = TRUE then
            s10:
                pay := TRUE;
                if card = TRUE then
                    if cheque < cardBonuses then
                        cardBonuses := cardBonuses - cheque;
                        cheque := 0;
                    else
                        cheque := cheque - cardBonuses;
                        cardBonuses := 0;
                    end if;
                end if;
                mloyal := FALSE;
        elsif main = FALSE /\ pay = TRUE then
            if cheque > rubles then
                s5: block := TRUE;
            else
                rubles := rubles - cheque;
                main := TRUE || recalc := FALSE;
            end if;
        elsif main = FALSE /\ weight = TRUE /\ stable = TRUE then
            rubles := rubles - productCost;
            main := TRUE || recalc := FALSE;
            weight := FALSE || stable := FALSE;
        else
            rubles := rubles - productCost;
            main := TRUE || recalc := FALSE;
        end if;
    end while;
end process

process Scales = "Scales" begin
s2:
    while(TRUE) do
        await main = FALSE /\ weight = TRUE;
        either 
            \*  balance on the scales has been established
            stable := TRUE || recalc := TRUE;
        or 
            \* otherwise return to menu
            stable := FALSE || main := TRUE || weight := FALSE;
        end either;
    end while;
end process

process Customer = "Customer" begin
s1:
    while(TRUE) do
        await main = TRUE;
        either
            \* put the product on the scales
            main := FALSE || weight := TRUE;
        or 
            \* buy bag
            main := FALSE || bag := TRUE || recalc := TRUE;
        or 
            \* pay - loyalty program come first
            main := FALSE || mloyal := TRUE || recalc := TRUE;
            either
                    card := TRUE
                or
                    card := FALSE
            end either;
        end either;
    end while;
end process

fair process Administrator = "Administrator" begin
    s5: while(TRUE) do
        await block = TRUE;
        main := TRUE || block := FALSE;
    end while;
end process;

end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES main, pay, block, mloyal, weight, bag, recalc, recalc2, card, 
          stable, rubles, productCost, cardBonuses, bagPrice, cheque, pc

(* define statement *)
PayAfterBonus == (mloyal => pay)
RemoveAfterAccess == (block => recalc)
StableWeight == (weight /\ stable => recalc)
BonusCard == (card => (mloyal /\ recalc))


vars == << main, pay, block, mloyal, weight, bag, recalc, recalc2, card, 
           stable, rubles, productCost, cardBonuses, bagPrice, cheque, pc >>

ProcSet == {"Register"} \cup {"Scales"} \cup {"Customer"}

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
        /\ productCost \in 1..5
        /\ cardBonuses \in 0..15
        /\ bagPrice \in 1..2
        /\ cheque = 0
        /\ pc = [self \in ProcSet |-> CASE self = "Register" -> "registerLoop"
                                        [] self = "Scales" -> "s2"
                                        [] self = "Customer" -> "s1"]

registerLoop == /\ pc["Register"] = "registerLoop"
                /\ recalc = TRUE
                /\ IF main = FALSE /\ bag = TRUE
                      THEN /\ pc' = [pc EXCEPT !["Register"] = "s8"]
                           /\ UNCHANGED << main, recalc, rubles >>
                      ELSE /\ IF main = FALSE /\ mloyal = TRUE
                                 THEN /\ pc' = [pc EXCEPT !["Register"] = "s10"]
                                      /\ UNCHANGED << main, recalc, rubles >>
                                 ELSE /\ IF main = FALSE /\ pay = TRUE
                                            THEN /\ IF cheque > rubles
                                                       THEN /\ pc' = [pc EXCEPT !["Register"] = "s5"]
                                                            /\ UNCHANGED << main, 
                                                                            recalc, 
                                                                            rubles >>
                                                       ELSE /\ rubles' = rubles - cheque
                                                            /\ /\ main' = TRUE
                                                               /\ recalc' = FALSE
                                                            /\ pc' = [pc EXCEPT !["Register"] = "registerLoop"]
                                            ELSE /\ pc' = [pc EXCEPT !["Register"] = "registerLoop"]
                                                 /\ UNCHANGED << main, recalc, 
                                                                 rubles >>
                /\ UNCHANGED << pay, block, mloyal, weight, bag, recalc2, card, 
                                stable, productCost, cardBonuses, bagPrice, 
                                cheque >>

s8 == /\ pc["Register"] = "s8"
      /\ cheque' = cheque + bagPrice
      /\ /\ bag' = FALSE
         /\ main' = TRUE
         /\ recalc' = FALSE
      /\ pc' = [pc EXCEPT !["Register"] = "registerLoop"]
      /\ UNCHANGED << pay, block, mloyal, weight, recalc2, card, stable, 
                      rubles, productCost, cardBonuses, bagPrice >>

s10 == /\ pc["Register"] = "s10"
       /\ IF card = TRUE
             THEN /\ IF cheque < cardBonuses
                        THEN /\ cardBonuses' = cardBonuses - cheque
                             /\ cheque' = 0
                        ELSE /\ cheque' = cheque - cardBonuses
                             /\ cardBonuses' = 0
             ELSE /\ TRUE
                  /\ UNCHANGED << cardBonuses, cheque >>
       /\ /\ mloyal' = FALSE
          /\ pay' = TRUE
       /\ pc' = [pc EXCEPT !["Register"] = "registerLoop"]
       /\ UNCHANGED << main, block, weight, bag, recalc, recalc2, card, stable, 
                       rubles, productCost, bagPrice >>

s5 == /\ pc["Register"] = "s5"
      /\ block' = TRUE
      /\ pc' = [pc EXCEPT !["Register"] = "registerLoop"]
      /\ UNCHANGED << main, pay, mloyal, weight, bag, recalc, recalc2, card, 
                      stable, rubles, productCost, cardBonuses, bagPrice, 
                      cheque >>

Register == registerLoop \/ s8 \/ s10 \/ s5

s2 == /\ pc["Scales"] = "s2"
      /\ main = FALSE /\ weight = TRUE
      /\ \/ /\ /\ recalc' = TRUE
               /\ stable' = TRUE
            /\ UNCHANGED <<main, weight>>
         \/ /\ /\ main' = TRUE
               /\ stable' = FALSE
               /\ weight' = FALSE
            /\ UNCHANGED recalc
      /\ pc' = [pc EXCEPT !["Scales"] = "s2"]
      /\ UNCHANGED << pay, block, mloyal, bag, recalc2, card, rubles, 
                      productCost, cardBonuses, bagPrice, cheque >>

Scales == s2

s1 == /\ pc["Customer"] = "s1"
      /\ main = TRUE
      /\ \/ /\ /\ main' = FALSE
               /\ weight' = TRUE
            /\ UNCHANGED <<mloyal, bag, recalc, card>>
         \/ /\ /\ bag' = TRUE
               /\ main' = FALSE
               /\ recalc' = TRUE
            /\ UNCHANGED <<mloyal, weight, card>>
         \/ /\ /\ main' = FALSE
               /\ mloyal' = TRUE
               /\ recalc' = TRUE
            /\ \/ /\ card' = TRUE
               \/ /\ card' = FALSE
            /\ UNCHANGED <<weight, bag>>
      /\ pc' = [pc EXCEPT !["Customer"] = "s1"]
      /\ UNCHANGED << pay, block, recalc2, stable, rubles, productCost, 
                      cardBonuses, bagPrice, cheque >>

Customer == s1

Next == Register \/ Scales \/ Customer
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Register)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

======================================
