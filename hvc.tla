\* Team 1) Abhinav Shukla,  2) Sachi Jain - 50134237
-------------------- MODULE hvc -------------------
EXTENDS Integers, TLC
CONSTANT N, STOP, EPS
ASSUME N \in Nat \ {0,1}
Procs == 1..N

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

(* Hybrid Logical Clocks algorithm
--algorithm hvc {
  variable pt = [j \in Procs |-> 0], msg= [j \in Procs |-> [k \in Procs |-> 0]], hvc= [j \in Procs |-> [k \in Procs |-> 0]];
  fair process (j \in Procs)
  variable  u = 0, v= 0;
  {
  J0:while (pt[self] < STOP)
   
      {
      either 
       Recv:{ 
         await(\A k \in Procs: pt[self] < pt[k]+ EPS); \* NTP clock sync
            pt[self] := pt[self] +1;
            hvc[self][self] := pt[self];
            u := 1;
            J1:while(u <= N)
            {
                if( u = self)
                {\*Take max of physcal time,hvc,msg
                 hvc[self][self] := SetMax({pt[self], msg [self][self]+1,  hvc[self][self]+1});
                }   
                 \*Take max of physical time-epsilon,hvc,msg
                else hvc[self][u] := SetMax({pt[self] - EPS, hvc[self][u], msg[self][u]}); 
                u := u+1;
            
            };
           
            } 
       or
       
       Send:{ 
         await(\A k \in Procs: pt[self] < pt[k]+ EPS); \* NTP clock sync
          
            pt[self] := pt[self] +1;
            hvc[self][self] := pt[self];
        
            v := 1;
            J2:while(v <= N)
            {
                if (v /= self)
                 hvc[self][v] := SetMax({hvc[self][v], pt[self] - EPS}); 
                v := v+1;
            
            };
            with (k \in Procs \ {self}) {msg[k] := hvc[self]};
            
            } 		 
      } 
  }
}
*)
\* BEGIN TRANSLATION
VARIABLES pt, msg, hvc, pc, u, v

vars == << pt, msg, hvc, pc, u, v >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ pt = [j \in Procs |-> 0]
        /\ msg = [j \in Procs |-> [k \in Procs |-> 0]]
        /\ hvc = [j \in Procs |-> [k \in Procs |-> 0]]
        (* Process j *)
        /\ u = [self \in Procs |-> 0]
        /\ v = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "J0"]

J0(self) == /\ pc[self] = "J0"
            /\ IF pt[self] < STOP
                  THEN /\ \/ /\ pc' = [pc EXCEPT ![self] = "Recv"]
                          \/ /\ pc' = [pc EXCEPT ![self] = "Send"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << pt, msg, hvc, u, v >>

Recv(self) == /\ pc[self] = "Recv"
              /\ (\A k \in Procs: pt[self] < pt[k]+ EPS)
              /\ pt' = [pt EXCEPT ![self] = pt[self] +1]
              /\ hvc' = [hvc EXCEPT ![self][self] = pt'[self]]
              /\ u' = [u EXCEPT ![self] = 1]
              /\ pc' = [pc EXCEPT ![self] = "J1"]
              /\ UNCHANGED << msg, v >>

J1(self) == /\ pc[self] = "J1"
            /\ IF u[self] <= N
                  THEN /\ IF u[self] = self
                             THEN /\ hvc' = [hvc EXCEPT ![self][self] = SetMax({pt[self], msg [self][self]+1,  hvc[self][self]+1})]
                             ELSE /\ hvc' = [hvc EXCEPT ![self][u[self]] = SetMax({pt[self] - EPS, hvc[self][u[self]], msg[self][u[self]]})]
                       /\ u' = [u EXCEPT ![self] = u[self]+1]
                       /\ pc' = [pc EXCEPT ![self] = "J1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "J0"]
                       /\ UNCHANGED << hvc, u >>
            /\ UNCHANGED << pt, msg, v >>

Send(self) == /\ pc[self] = "Send"
              /\ (\A k \in Procs: pt[self] < pt[k]+ EPS)
              /\ pt' = [pt EXCEPT ![self] = pt[self] +1]
              /\ hvc' = [hvc EXCEPT ![self][self] = pt'[self]]
              /\ v' = [v EXCEPT ![self] = 1]
              /\ pc' = [pc EXCEPT ![self] = "J2"]
              /\ UNCHANGED << msg, u >>

J2(self) == /\ pc[self] = "J2"
            /\ IF v[self] <= N
                  THEN /\ IF v[self] /= self
                             THEN /\ hvc' = [hvc EXCEPT ![self][v[self]] = SetMax({hvc[self][v[self]], pt[self] - EPS})]
                             ELSE /\ TRUE
                                  /\ hvc' = hvc
                       /\ v' = [v EXCEPT ![self] = v[self]+1]
                       /\ pc' = [pc EXCEPT ![self] = "J2"]
                       /\ msg' = msg
                  ELSE /\ \E k \in Procs \ {self}:
                            msg' = [msg EXCEPT ![k] = hvc[self]]
                       /\ pc' = [pc EXCEPT ![self] = "J0"]
                       /\ UNCHANGED << hvc, v >>
            /\ UNCHANGED << pt, u >>

j(self) == J0(self) \/ Recv(self) \/ J1(self) \/ Send(self) \/ J2(self)

Next == (\E self \in Procs: j(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(j(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Boundedness
TypeOK == (\A k \in Procs: hvc[k][k] >= pt[k])
Sync == (\A k,m \in Procs: hvc[k][m] <= pt[k]+EPS)
Bound == (\A k,m \in Procs: hvc[k][k] >= hvc[m][k])
Sync2 == (\A k,m \in Procs: pt[k] <= pt[m] +EPS)



\* Stabilization
==================================================
