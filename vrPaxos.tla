---------------------------- MODULE vrPaxos -------------------------------
EXTENDS Integers, TLC, FiniteSets, Reals
-----------------------------------------------------------------------------
CONSTANT Acceptor, Leader, Replica
-----------------------------------------------------------------------------

(***********

--algorithm vrPaxos 
{
  variables slot_num  = [r \in Replica |-> 1],
            ballot_num = [a \in Acceptor |-> <<0,0>>],
            accepted = [a \in Acceptor |-> {} ],
            usedS=0,
            (* ballot = 1,*)
            ballot = [l \in Leader |-> <<1,l>>],
            received_b = [l \in Leader |-> <<0,0>>],
            (*
            msgs = {[type |-> "1b", bal |-> 1, 
                        accepted |-> {<<1,1,1>>,<<2,1,1>>,<<3,1,1>>}],
                    [ type |-> "propose", slot |-> 3 ],
                    [ type |-> "2a", bal |-> 1, slot |-> 2, p |-> 1 ]
                    },
            *)
            msgs = { [ type |-> "request", p |-> 3 ], 
                     [ type |-> "request", p |-> 4 ]
                   },
            chosen = {}
  define
  {
        (***************************************************************************)
        (* Operator aGreaterThanb to compare two tuples <<a1,a2>> & <<b1,b2>>.     *)
        (* Function returns TRUE if a is greater than b.                           *)
        (***************************************************************************)
        aGrtb(a,b) == \/ a[1] > b[1]
                      \/ /\ a[1] = b[1]
                         /\ a[2] > b[2]

        (***************************************************************************)
        (* Operator aGreaterThanOrEqualb to compare two tuples <<a1,a2>>           *)
        (* & <<b1,b2>>. Function returns TRUE if a is greater than or equal to b.  *)
        (***************************************************************************)
        aGrtEqb(a,b) == \/ a[1] > b[1]
                        \/ /\ a[1] = b[1]
                           /\ a[2] >= b[2]

        (************************************************************)
        (* This set represents the set of 2a messages that will be  *)
        (* sent by the leader. When a leader receives a 'propose'   *)
        (* for a slot 's', it checks to see if it has already sent  *)
        (* a 2a message for it's current ballot number for that     *)
        (* slot. If not, it adds a '2a' message for this slot to    *)
        (* the queue for sending.                                   *)
        (************************************************************)
        proposalMsgs == { m \in msgs : /\ m.type = "propose" }
        2aMsgs(l) == { m \in msgs : /\ m.type = "2a" /\ m.bal = ballot[l] }
        send2aSet(l) == { m \in proposalMsgs : ~ \E m1 \in 2aMsgs(l) :  /\ m1.slot = m.slot }  
        
        (*******************************************************************)
        (* Below we calculate bmax as outlined in the pseudo-code. We do   *)
        (* this by first finding all 1b messages whose ballot match the    *)
        (* leader's current ballot. The pvals set represents the union     *)
        (* of all accepted values received in these 1b messages (from      *)
        (* acceptors). We then filter the pvals to find the <<slot,        *)
        (* command>> tuples with the highest ballot numbers. These         *)
        (* tuples form our bmax set.                                       *)
        (*******************************************************************)
        1bMsgs(l) == { m \in msgs : m.type = "1b" /\ m.bal = ballot[l] } 
        pvals(l) == UNION { m.accepted : m \in 1bMsgs(l) }
        
        partial_bmax(l) == { pvl \in pvals(l) : ~ \E pvl1 \in pvals(l) : pvl[2] = pvl1[2] /\ aGrtb(pvl1[1], pvl[1]) } (* Same slot and higher ballot *)
        bmax(l) == { <<s[2],s[3]>> : s \in partial_bmax(l) }
  
        (*******************************************************************)
        (* When a Leader receives a 2b message containing it's current     *)
        (* ballot, it checks if it has received 2b messages in the         *)
        (* current ballot at THAT slot from a majority of the acceptors,   *)
        (* and if so, it sends a decision to the replicas                  *)
        (* - <<slot, command>>. Here, spPairs represents the set of        *)
        (* <<slot, command>> pairs it recieved from 2b messages            *)
        (* bearing the Leader's current ballot. The Leader uses            *)
        (* these pairs to check if a majority of the acceptors             *)
        (* have sent 2b replies for each of these slots mentioned in the   *)
        (* pairs above.                                                    *)
        (*******************************************************************)
        2bMsgs(l) == { m \in msgs : /\ m.type = "2b" /\ m.bal = ballot[l] }
        spPairs(l) == { <<m.slot,m.p>> : m \in 2bMsgs(l) }
        AcceptorsSent2b(l,slot) == { a \in Acceptor : \E m \in 2bMsgs(l) : m.from = a /\ m.slot = slot } 
        
        (*******************************************************************)
        (* This represents the set of acceptors that have sent 1b replies  *)
        (* with Leader's current ballot.                                   *)
        (*******************************************************************)
        AcceptorsSent1b(l) == { a \in Acceptor : \E m \in 1bMsgs(l) : m.from = a } 
        
        preemptSet(l) == { m \in msgs : /\ (m.type = "1b" \/ m.type = "2b") /\  aGrtb(m.bal,ballot[l]) } (* m.bal > ballot[l] } *)
        
        myset == {1,2,3}
        myset1 == {}
        p2aBatch(l,s) == {[ type |-> "2a" ,  bal |-> ballot[l] , slot |-> t[1] , p |-> t[2] ] : t \in bmax(l) }
        
        decisionSet(r) == { m \in msgs : m.type = "decision" /\ m.slot = slot_num[r] }

        proposeOrDecisionMsgs == {m \in msgs : /\ (m.type = "propose" \/ m.type = "decision") }
        proposeOrDecisionSlots == { m.slot : m \in proposeOrDecisionMsgs } \cup {0}
        (* MaxsSet == { v \in proposeOrDecisionSlots : ~ \E v1 \in proposeOrDecisionSlots : v < v1 } (* Return the maximum. *) *)
        (* MaxS == CHOOSE v : v \in MaxsSet *)
        test == { m \in msgs : m.type = "propose" }
        
        proposeOrDecisionMsgs1(slot) == {m \in msgs : /\ (m.type = "propose" \/ m.type = "decision")
                                                  /\ m.slot = slot }
        
        (* Set of all slots that do not have a corresponding propose/decision message. *)
        unusedSlots == {slot \in 1..usedS+1+1 : ~ \E m \in msgs : /\ (m.type = "propose" \/ m.type = "decision")
                                                         /\ m.slot = slot }    
        (* MinSet == { slot \in unusedSlots : ~ \E slot1 \in unusedSlots : slot1 < slot } *)
        
        (* MinS == CHOOSE v : v \in MinSet *)
        
        p1aMsgs == { m \in msgs : m.type = "1a" } (* Issue : Acceptor might end up repeatedly responding to 1a message. *)
        p2aMsgs == { m \in msgs : m.type = "2a"  } (* Same Issue *)  
        
        proposedMsgs(p) == { m \in msgs : m.type = "propose" /\ m.p = p }
        decisionMsgs(slot) == { m \in msgs : m.type = "decision" /\ m.slot = slot }
        requestReceived == { m \in msgs : m.type = "request" }
        
        (*******************************************************************)
        (* R1: Two different commands are never decided for the same slot: *)
        (* ∀s, ρ1 , ρ2 , c1 , c2 : s, c1 ∈ ρ1 .decisions ∧ s, c2 ∈         *)
        (* ρ2.decisions ⇒ c1 = c2.                                         *)
        (*                                                                 *)
        (* :: In our improved replica, each replica does not store the     *)
        (* set of decisions it makes. However, when a replica makes a      *)
        (* decision, it performs the operation on the state and sends      *)
        (* the result of the operation to the client. In my                *)
        (* specification, when a replica makes a decision for a slot,      *)
        (* it pushes a <<slot, command>> tuple into a global 'chosen'      *)
        (* set. So this invariant thus reduces to checking if:             *)
        (*     - For a given s, there MUST NOT BE 2 tuples                 *)
        (*     <<s,p1>> & <<s,p2>>, in 'chosen' such that p1 != p2.        *)
        (*                                                                 *)
        (*******************************************************************)
        R1 == ~ \E t1 \in chosen : \E t2 \in chosen : t1[1] = t2[1] /\ t1[2] # t2[2] 

        (***************************************************************************)
        (* R2: All commands up to slot_num are in the set of decisions:            *)
        (* ∀ρ, s : 1 ≤ s < ρ.slot num ⇒ (∃c : s, c ∈ ρ.decisions)                  *)
        (***************************************************************************)    
        used_slots(r) == {s \in 1..slot_num[r]: s < slot_num[r]}
        R2 == \A r \in Replica : \A s \in used_slots(r) : \E dec \in chosen : dec[1] = s
        
        (*******************************************************************)
        (* A0: for all b, b , s, c, c , if pvalue b, s, c                  *)
        (* and pvalue b , s, c are both accepted by a                      *)
        (* majority of acceptors, then c = c.                              *)
        (* - pvalSet is the set of all pvals that were                     *)
        (* accepted by any acceptor.                                       *)
        (* - acceptorList(pval) is the list of acceptors that              *)
        (* accepted pval.                                                  *)
        (* - majorityAcceptedPvals is the set of pvals accepted by a       *)
        (* majority set of acceptors.                                      *)
        (*******************************************************************)
        pvalSet == UNION { accepted[a] : a \in Acceptor } (* Set of all pvals *)
        acceptorsList(pval) == {a \in Acceptor : pval \in accepted[a] }
        majorityAcceptedPvals == {pval \in pvalSet : Cardinality( acceptorsList(pval) ) > Cardinality(Acceptor) \div 2 }
        
        A0 == \A pval1,pval2 \in majorityAcceptedPvals : pval1[1] = pval2[1] /\ pval1[2] = pval2[2] => pval1[3] = pval2[3]

        (* A1 == \A a \in Acceptor : aGrtEqb(ballot_num'[a],ballot_num[a]) *)
        
        (*******************************************************************)
        (* A4: Suppose α and α are acceptors, with b, s, c ∈               *)
        (* α.accepted and b, s, c ∈ α .accepted. Then                      *)
        (* c = c . Informally, given a particular ballot num-              *)
        (* ber and slot number, there can be at most one                   *)
        (* proposed command under consideration by the                     *)
        (* set of acceptors.                                               *)
        (*                                                                 *)
        (* This boils down to ensuring that for all possible               *)
        (* pairs of acceptors α & α',                                      *)
        (*     - For all elements in accepted[α] <<b,s,p>>,                *)
        (*      there must not exist a <<b,s,p'>> such that                *)
        (*      p # p'.                                                    *)
        (*******************************************************************)
        A4 == \A a1 \in Acceptor : \A a2 \in Acceptor : \A acc1 \in accepted[a1] : ~ \E acc2 \in accepted[a2] : /\ acc1[1] = acc2[1] 
                                                                                                                /\ acc1[2] = acc2[2]
                                                                                                                /\ acc1[3] # acc2[3]

        (*******************************************************************)
        (* A5: Suppose that for each α among a majority of                 *)
        (* acceptors, b, s, c ∈ α.accepted. If b' > b and                  *)
        (* b , s, c ∈ α' .accepted, then c = c.                            *)
        (*                                                                 *)
        (* For this we take all pvals that were accepted by a              *)
        (* majority of Acceptors and ensure for all other                  *)
        (* pvals in pvalSet with same slot and higher ballot,              *)
        (* must have the same command.                                     *)
        (*******************************************************************)
        A5 == \A pval \in majorityAcceptedPvals : \A pval1 \in pvalSet : /\ pval1[2] = pval[2]
                                                                         /\ aGrtb(pval1[1],pval[1]) 
                                                                         => pval1[3] = pval[3]                                                                   
        
        (***************************************************************************)
        (* L1 : For any b and s, at most one commander is                          *)
        (* spawned;                                                                *)
        (***************************************************************************)
        2aMsgSet == { m \in msgs : /\ m.type = "2a" }
        L1 == \A m1,m2 \in 2aMsgSet : /\ m1.bal = m2.bal
                                      /\ m1.slot = m2.slot
                                      => m1.p = m2.p 
        
        (***************************************************************************)
        (* L2: Suppose that for each α among a majority of                         *)
        (* acceptors b, s, c ∈ α.accepted. If b' > b and a                         *)
        (* commander is spawned for b' , s, c' , then c = c' .                     *)
        (*                                                                         *)
        (* Since we do not have any explicit commanders in                         *)
        (* this spec, we check to see if this condition                            *)
        (* holds when a 2a message is sent. i.e.                                   *)
        (* for each α among a majority of                                          *)
        (* acceptors b, s, c ∈ α.accepted. If b' > b and a                         *)
        (* 2a message is sent for b',s, c' , then c = c' .                       *)
        (*                                                                         *)
        (***************************************************************************)  
        2aMsgsBySlot(slot) == { m \in msgs : /\ m.type = "2a" /\ m.slot = slot }
        L2 == \A pval \in majorityAcceptedPvals : \A m \in 2aMsgsBySlot(pval[2]) : /\ aGrtb(m.bal,pval[1]) 
                                                                                   => m.p = pval[3]                                                                   
  }

  macro P2a(l)
  {
    print "Leader :: Sending a Phase 2a message.";
    msgs := msgs \cup {[ type |-> "2a" ,  bal |-> ballot[l] , slot |-> t[1] , p |-> t[2] ] : t \in bmax(l) };
  }
  
  macro P1a(l)
  {
    print "Leader :: Sending a Phase 1a message.";
    msgs := msgs \cup {[ type |-> "1a", bal |-> ballot[l] ]};
  }  
  
  macro send(m)
  {
    msgs := msgs \cup {m}; 
  }

  process (r \in Replica) 
    variable minS;
  {
        (*       
        while true:  # used await-or, instead of for-if/while in SSS 12 paper *)
        repl:while(TRUE)
        {
          print "Replica: Start Of while..";

          (*
          await some rcvd('request',p)
                | (all sent('propose',s,=p) | rcvd('decision',s,p2) and p2!=p): *)
          either with( m \in requestReceived )
          {
            print "Replica: Got a request..";
            when /\ \A m1 \in proposedMsgs(m.p) : \E m2 \in decisionMsgs(m1.slot) : m2.p # m1.p;
            print "Replica: Cool. I will send a propose..";
              
            (*
            useds = max({s: sent('propose',s,_) or rcvd('decision',s,_)} or {0}) *)
            usedS := CHOOSE i \in proposeOrDecisionSlots : \A j \in proposeOrDecisionSlots : j <= i; 
            (* usedS := CHOOSE v \in MaxsSet : TRUE; *)
            
            print <<"UsedS",usedS>>;    
            print <<"unused slots",unusedSlots>>;
            print <<"Range",1..usedS+1+1>>;
            
            (*
            s = min({s in 1..useds + 1
                     | not (sent('propose',s,_) or rcvd('decision',s,_))}) *)
            minS := CHOOSE i \in unusedSlots : \A j \in unusedSlots : j >= i;
            (* minS :=  CHOOSE v \in MinSet : TRUE; *)
    
            print <<"minS",minS>>;    

            (*
            send ('propose', s, p) to leaders *)
            msgs := msgs \cup {[ type |-> "propose" , slot |-> minS , p |-> m.p ]};
            
            print <<"After Propose",msgs>>;
            print <<"Propose/Decision Slots:",proposeOrDecisionSlots>>;
            print <<"Propose/Decision Msgs:",test>>;
            
          }
            
          (*
          or some rcvd('decision', =slot_num, p): *)
          or with( m \in decisionSet(self) )
          {
            print "Replica: DECISION UPDATE.";
            print <<"p",m.p>>;
            print <<"slot_num",slot_num>>;
            print <<"s",m.slot>>;
            print msgs;
            (*
            if not exists rcvd('decison', s, =p) | s < slot_num): *)
            if( ~ \E m1 \in msgs : m1.type = "decision" /\ m.p = m1.p /\ m1.slot < slot_num[self] )
            {

              (*  
              client, cmd_id, op = p
              state, result = op(state)
              send ('response', cmd_id, result) to client *)
              
              chosen := chosen \cup {<<m.slot,m.p>>};
              print <<"CHOSEN UPDATED TO:",chosen>>;
              
              (* skip; *)
            };
            
            (*
            slot_num += 1 *)
            slot_num[self] := slot_num[self] + 1;
          }
        }    
        
  }

  process (leader \in Leader) 
   variable active;
  {
     (* while true: *)
        ldr:while(TRUE)
        {
       (* send ('p1a', ballot) to acceptors *)
         (* P1a(); *)
        
        ldr1:print "Leader1 :: Sending a Phase 1a message.";
             P1a(self);
             print msgs;
        
       (* await numberof( {a: rcvd(('p1b', =ballot, _) from a)} )  > numberOf( acceptors/2 ): *)
          ldr2:either 
          {
            when Cardinality(AcceptorsSent1b(self)) >= 1;(* Cardinality( Acceptor )/2 ; *)
    
            (*
            for (s,p) in bmax({t: rcvd('p1b', =ballot, accepted), t in accepted}):
              send ('p2a', ballot, s, p) to acceptors *)
            sndp2a:P2a(self);
              
            active := TRUE;
            
            (*    
            while true: *)
            ldr3:while(active)
            {
              (*
              await some rcvd('propose', s, p) | not sent('p2a', ballot, s, _):
                send ('p2a', ballot, s, p) to acceptors *)
              either with( m \in send2aSet(self) ) 
                     {
                        send( [ type |-> "2a" ,  bal |-> ballot[self] , slot |-> m.slot , p |-> m.p ] );
                        print <<"THE DARK ZONE",msgs>>;
                     }
              (*  
              or some rcvd('p2b', =ballot, s, p)
                 | #{a: rcvd(('p2b', =ballot, =s) from a)} > #acceptors/2:
                send ('decision', s, p) to replicas *)
              or with( t \in spPairs(self) )
              {
                  when /\ Cardinality( AcceptorsSent2b(self,t[1]) ) >= 1;(* Cardinality( Acceptor )/2 ; *)
                  print "Leader: Sending a DECISION.";
                  send( [ type |-> "decision" , slot |-> t[1] , p |-> t[2] ] );
              }
    
              (* 
              or some rcvd('p2b', b, _) or rcvd('p1b', b, _) | b > ballot:
                break *)
              or with(  m \in preemptSet(self) )
              {
                received_b[self] := m.bal;
                active := FALSE; (* break *)
              }
    
    
            }    
          }  
          (*
          or some rcvd('p1b', b, _) or rcvd('p2b', b, _) | b > ballot:
            pass *)
          or with(  m \in preemptSet(self) )
          {
            received_b[self] := m.bal;
          };
          
          (*  
          ballot = (ballot[0]+1, self) *)
          pmpt:ballot[self] := <<received_b[self][1]+1, self>>;            
          (* pmpt:ballot := received_b+1;   (* since only a single leader *) *)
        }
    
    }
  
  (**
      process Acceptor()
      var ballot num := ⊥, accepted := ∅;
    
      for ever
        switch receive()
          case p1a, λ, b :
            if b > ballot num then
              ballot num := b;
            end if;
            send(λ, p1b, self(), ballot num, accepted );
          end case
          case p2a, λ, b, s, c :
            if b ≥ ballot num then
              ballot num := b;
              accepted := accepted ∪ { b, s, c };
            end if
            send(λ, p2b, self(), ballot num );
          end case
        end switch
      end for
    end process
  **)  
  process (a \in Acceptor)
  {
      acc:while(TRUE)
      {
        print "Acceptor:Entered Acceptor While..";
        either with( m \in p1aMsgs )
        {
            print "Acceptor: Received p1a.";
            if( aGrtb(m.bal,ballot_num[self]) )   (* m.bal > ballot_num[self] ) *)
            {
              assert aGrtb(m.bal,ballot_num[self]); (* A1 : Assert that only strictly increasing ballot numbers are ADOPTED. *) 
              ballot_num[self] := m.bal;
            };  

            print "Acceptor: Sending p1b.";
            send( [ type |-> "1b" , bal |-> ballot_num[self] , accepted |-> accepted[self] , from |-> self ] );
        }
        or with( m \in p2aMsgs )
           {
                print "Acceptor: Received p2a.";
                if( aGrtEqb(m.bal,ballot_num[self])  )(* m.bal >= ballot_num[self] ) *)
                {
                  ballot_num[self] := m.bal;
                  accepted[self] := accepted[self] \cup {<< m.bal, m.slot, m.p >>} ;   
                  assert m.bal = ballot_num[self];  (* A2: an acceptor α can only add b, s, c to α.accepted
                                                       (i.e., accept b, s, c ) if b = ballot num; *)
                };

                print "Acceptor: Sending p2b.";
                send( [ type |-> "2b" , bal |-> ballot_num[self] , from |-> self, slot |-> m.slot, p |-> m.p  ] );
           }  
      }
  }

}

************)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES slot_num, ballot_num, accepted, usedS, ballot, received_b, msgs, 
          chosen, pc

(* define statement *)
aGrtb(a,b) == \/ a[1] > b[1]
              \/ /\ a[1] = b[1]
                 /\ a[2] > b[2]





aGrtEqb(a,b) == \/ a[1] > b[1]
                \/ /\ a[1] = b[1]
                   /\ a[2] >= b[2]









proposalMsgs == { m \in msgs : /\ m.type = "propose" }
2aMsgs(l) == { m \in msgs : /\ m.type = "2a" /\ m.bal = ballot[l] }
send2aSet(l) == { m \in proposalMsgs : ~ \E m1 \in 2aMsgs(l) :  /\ m1.slot = m.slot }










1bMsgs(l) == { m \in msgs : m.type = "1b" /\ m.bal = ballot[l] }
pvals(l) == UNION { m.accepted : m \in 1bMsgs(l) }

partial_bmax(l) == { pvl \in pvals(l) : ~ \E pvl1 \in pvals(l) : pvl[2] = pvl1[2] /\ aGrtb(pvl1[1], pvl[1]) }
bmax(l) == { <<s[2],s[3]>> : s \in partial_bmax(l) }













2bMsgs(l) == { m \in msgs : /\ m.type = "2b" /\ m.bal = ballot[l] }
spPairs(l) == { <<m.slot,m.p>> : m \in 2bMsgs(l) }
AcceptorsSent2b(l,slot) == { a \in Acceptor : \E m \in 2bMsgs(l) : m.from = a /\ m.slot = slot }





AcceptorsSent1b(l) == { a \in Acceptor : \E m \in 1bMsgs(l) : m.from = a }

preemptSet(l) == { m \in msgs : /\ (m.type = "1b" \/ m.type = "2b") /\  aGrtb(m.bal,ballot[l]) }

myset == {1,2,3}
myset1 == {}
p2aBatch(l,s) == {[ type |-> "2a" ,  bal |-> ballot[l] , slot |-> t[1] , p |-> t[2] ] : t \in bmax(l) }

decisionSet(r) == { m \in msgs : m.type = "decision" /\ m.slot = slot_num[r] }

proposeOrDecisionMsgs == {m \in msgs : /\ (m.type = "propose" \/ m.type = "decision") }
proposeOrDecisionSlots == { m.slot : m \in proposeOrDecisionMsgs } \cup {0}


test == { m \in msgs : m.type = "propose" }

proposeOrDecisionMsgs1(slot) == {m \in msgs : /\ (m.type = "propose" \/ m.type = "decision")
                                          /\ m.slot = slot }


unusedSlots == {slot \in 1..usedS+1+1 : ~ \E m \in msgs : /\ (m.type = "propose" \/ m.type = "decision")
                                                 /\ m.slot = slot }




p1aMsgs == { m \in msgs : m.type = "1a" }
p2aMsgs == { m \in msgs : m.type = "2a"  }

proposedMsgs(p) == { m \in msgs : m.type = "propose" /\ m.p = p }
decisionMsgs(slot) == { m \in msgs : m.type = "decision" /\ m.slot = slot }
requestReceived == { m \in msgs : m.type = "request" }

















R1 == ~ \E t1 \in chosen : \E t2 \in chosen : t1[1] = t2[1] /\ t1[2] # t2[2]





used_slots(r) == {s \in 1..slot_num[r]: s < slot_num[r]}
R2 == \A r \in Replica : \A s \in used_slots(r) : \E dec \in chosen : dec[1] = s












pvalSet == UNION { accepted[a] : a \in Acceptor }
acceptorsList(pval) == {a \in Acceptor : pval \in accepted[a] }
majorityAcceptedPvals == {pval \in pvalSet : Cardinality( acceptorsList(pval) ) > Cardinality(Acceptor) \div 2 }

A0 == \A pval1,pval2 \in majorityAcceptedPvals : pval1[1] = pval2[1] /\ pval1[2] = pval2[2] => pval1[3] = pval2[3]

















A4 == \A a1 \in Acceptor : \A a2 \in Acceptor : \A acc1 \in accepted[a1] : ~ \E acc2 \in accepted[a2] : /\ acc1[1] = acc2[1]
                                                                                                        /\ acc1[2] = acc2[2]
                                                                                                        /\ acc1[3] # acc2[3]











A5 == \A pval \in majorityAcceptedPvals : \A pval1 \in pvalSet : /\ pval1[2] = pval[2]
                                                                 /\ aGrtb(pval1[1],pval[1])
                                                                 => pval1[3] = pval[3]





2aMsgSet == { m \in msgs : /\ m.type = "2a" }
L1 == \A m1,m2 \in 2aMsgSet : /\ m1.bal = m2.bal
                              /\ m1.slot = m2.slot
                              => m1.p = m2.p














2aMsgsBySlot(slot) == { m \in msgs : /\ m.type = "2a" /\ m.slot = slot }
L2 == \A pval \in majorityAcceptedPvals : \A m \in 2aMsgsBySlot(pval[2]) : /\ aGrtb(m.bal,pval[1])
                                                                           => m.p = pval[3]

VARIABLES minS, active

vars == << slot_num, ballot_num, accepted, usedS, ballot, received_b, msgs, 
           chosen, pc, minS, active >>

ProcSet == (Replica) \cup (Leader) \cup (Acceptor)

Init == (* Global variables *)
        /\ slot_num = [r \in Replica |-> 1]
        /\ ballot_num = [a \in Acceptor |-> <<0,0>>]
        /\ accepted = [a \in Acceptor |-> {} ]
        /\ usedS = 0
        /\ ballot = [l \in Leader |-> <<1,l>>]
        /\ received_b = [l \in Leader |-> <<0,0>>]
        /\ msgs = { [ type |-> "request", p |-> 3 ],
                    [ type |-> "request", p |-> 4 ]
                  }
        /\ chosen = {}
        (* Process r *)
        /\ minS = [self \in Replica |-> defaultInitValue]
        (* Process leader *)
        /\ active = [self \in Leader |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in Replica -> "repl"
                                        [] self \in Leader -> "ldr"
                                        [] self \in Acceptor -> "acc"]

repl(self) == /\ pc[self] = "repl"
              /\ PrintT("Replica: Start Of while..")
              /\ \/ /\ \E m \in requestReceived:
                         /\ PrintT("Replica: Got a request..")
                         /\ /\ \A m1 \in proposedMsgs(m.p) : \E m2 \in decisionMsgs(m1.slot) : m2.p # m1.p
                         /\ PrintT("Replica: Cool. I will send a propose..")
                         /\ usedS' = (CHOOSE i \in proposeOrDecisionSlots : \A j \in proposeOrDecisionSlots : j <= i)
                         /\ PrintT(<<"UsedS",usedS'>>)
                         /\ PrintT(<<"unused slots",unusedSlots>>)
                         /\ PrintT(<<"Range",1..usedS'+1+1>>)
                         /\ minS' = [minS EXCEPT ![self] = CHOOSE i \in unusedSlots : \A j \in unusedSlots : j >= i]
                         /\ PrintT(<<"minS",minS'[self]>>)
                         /\ msgs' = (msgs \cup {[ type |-> "propose" , slot |-> minS'[self] , p |-> m.p ]})
                         /\ PrintT(<<"After Propose",msgs'>>)
                         /\ PrintT(<<"Propose/Decision Slots:",proposeOrDecisionSlots>>)
                         /\ PrintT(<<"Propose/Decision Msgs:",test>>)
                    /\ UNCHANGED <<slot_num, chosen>>
                 \/ /\ \E m \in decisionSet(self):
                         /\ PrintT("Replica: DECISION UPDATE.")
                         /\ PrintT(<<"p",m.p>>)
                         /\ PrintT(<<"slot_num",slot_num>>)
                         /\ PrintT(<<"s",m.slot>>)
                         /\ PrintT(msgs)
                         /\ IF ~ \E m1 \in msgs : m1.type = "decision" /\ m.p = m1.p /\ m1.slot < slot_num[self]
                               THEN /\ chosen' = (chosen \cup {<<m.slot,m.p>>})
                                    /\ PrintT(<<"CHOSEN UPDATED TO:",chosen'>>)
                               ELSE /\ TRUE
                                    /\ UNCHANGED chosen
                         /\ slot_num' = [slot_num EXCEPT ![self] = slot_num[self] + 1]
                    /\ UNCHANGED <<usedS, msgs, minS>>
              /\ pc' = [pc EXCEPT ![self] = "repl"]
              /\ UNCHANGED << ballot_num, accepted, ballot, received_b, active >>

r(self) == repl(self)

ldr(self) == /\ pc[self] = "ldr"
             /\ pc' = [pc EXCEPT ![self] = "ldr1"]
             /\ UNCHANGED << slot_num, ballot_num, accepted, usedS, ballot, 
                             received_b, msgs, chosen, minS, active >>

ldr1(self) == /\ pc[self] = "ldr1"
              /\ PrintT("Leader1 :: Sending a Phase 1a message.")
              /\ PrintT("Leader :: Sending a Phase 1a message.")
              /\ msgs' = (msgs \cup {[ type |-> "1a", bal |-> ballot[self] ]})
              /\ PrintT(msgs')
              /\ pc' = [pc EXCEPT ![self] = "ldr2"]
              /\ UNCHANGED << slot_num, ballot_num, accepted, usedS, ballot, 
                              received_b, chosen, minS, active >>

ldr2(self) == /\ pc[self] = "ldr2"
              /\ \/ /\ Cardinality(AcceptorsSent1b(self)) >= 1
                    /\ pc' = [pc EXCEPT ![self] = "sndp2a"]
                    /\ UNCHANGED received_b
                 \/ /\ \E m \in preemptSet(self):
                         received_b' = [received_b EXCEPT ![self] = m.bal]
                    /\ pc' = [pc EXCEPT ![self] = "pmpt"]
              /\ UNCHANGED << slot_num, ballot_num, accepted, usedS, ballot, 
                              msgs, chosen, minS, active >>

sndp2a(self) == /\ pc[self] = "sndp2a"
                /\ PrintT("Leader :: Sending a Phase 2a message.")
                /\ msgs' = (msgs \cup {[ type |-> "2a" ,  bal |-> ballot[self] , slot |-> t[1] , p |-> t[2] ] : t \in bmax(self) })
                /\ active' = [active EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "ldr3"]
                /\ UNCHANGED << slot_num, ballot_num, accepted, usedS, ballot, 
                                received_b, chosen, minS >>

ldr3(self) == /\ pc[self] = "ldr3"
              /\ IF active[self]
                    THEN /\ \/ /\ \E m \in send2aSet(self):
                                    /\ msgs' = (msgs \cup {([ type |-> "2a" ,  bal |-> ballot[self] , slot |-> m.slot , p |-> m.p ])})
                                    /\ PrintT(<<"THE DARK ZONE",msgs'>>)
                               /\ UNCHANGED <<received_b, active>>
                            \/ /\ \E t \in spPairs(self):
                                    /\ /\ Cardinality( AcceptorsSent2b(self,t[1]) ) >= 1
                                    /\ PrintT("Leader: Sending a DECISION.")
                                    /\ msgs' = (msgs \cup {([ type |-> "decision" , slot |-> t[1] , p |-> t[2] ])})
                               /\ UNCHANGED <<received_b, active>>
                            \/ /\ \E m \in preemptSet(self):
                                    /\ received_b' = [received_b EXCEPT ![self] = m.bal]
                                    /\ active' = [active EXCEPT ![self] = FALSE]
                               /\ msgs' = msgs
                         /\ pc' = [pc EXCEPT ![self] = "ldr3"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "pmpt"]
                         /\ UNCHANGED << received_b, msgs, active >>
              /\ UNCHANGED << slot_num, ballot_num, accepted, usedS, ballot, 
                              chosen, minS >>

pmpt(self) == /\ pc[self] = "pmpt"
              /\ ballot' = [ballot EXCEPT ![self] = <<received_b[self][1]+1, self>>]
              /\ pc' = [pc EXCEPT ![self] = "ldr"]
              /\ UNCHANGED << slot_num, ballot_num, accepted, usedS, 
                              received_b, msgs, chosen, minS, active >>

leader(self) == ldr(self) \/ ldr1(self) \/ ldr2(self) \/ sndp2a(self)
                   \/ ldr3(self) \/ pmpt(self)

acc(self) == /\ pc[self] = "acc"
             /\ PrintT("Acceptor:Entered Acceptor While..")
             /\ \/ /\ \E m \in p1aMsgs:
                        /\ PrintT("Acceptor: Received p1a.")
                        /\ IF aGrtb(m.bal,ballot_num[self])
                              THEN /\ Assert(aGrtb(m.bal,ballot_num[self]), 
                                             "Failure of assertion at line 434, column 15.")
                                   /\ ballot_num' = [ballot_num EXCEPT ![self] = m.bal]
                              ELSE /\ TRUE
                                   /\ UNCHANGED ballot_num
                        /\ PrintT("Acceptor: Sending p1b.")
                        /\ msgs' = (msgs \cup {([ type |-> "1b" , bal |-> ballot_num'[self] , accepted |-> accepted[self] , from |-> self ])})
                   /\ UNCHANGED accepted
                \/ /\ \E m \in p2aMsgs:
                        /\ PrintT("Acceptor: Received p2a.")
                        /\ IF aGrtEqb(m.bal,ballot_num[self])
                              THEN /\ ballot_num' = [ballot_num EXCEPT ![self] = m.bal]
                                   /\ accepted' = [accepted EXCEPT ![self] = accepted[self] \cup {<< m.bal, m.slot, m.p >>}]
                                   /\ Assert(m.bal = ballot_num'[self], 
                                             "Failure of assertion at line 448, column 19.")
                              ELSE /\ TRUE
                                   /\ UNCHANGED << ballot_num, accepted >>
                        /\ PrintT("Acceptor: Sending p2b.")
                        /\ msgs' = (msgs \cup {([ type |-> "2b" , bal |-> ballot_num'[self] , from |-> self, slot |-> m.slot, p |-> m.p  ])})
             /\ pc' = [pc EXCEPT ![self] = "acc"]
             /\ UNCHANGED << slot_num, usedS, ballot, received_b, chosen, minS, 
                             active >>

a(self) == acc(self)

Next == (\E self \in Replica: r(self))
           \/ (\E self \in Leader: leader(self))
           \/ (\E self \in Acceptor: a(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Fri Nov 22 03:12:07 EST 2013 by anthony
\* Last modified Tue Feb 08 12:09:41 PST 2011 by lamport
