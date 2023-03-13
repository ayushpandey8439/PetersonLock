--------------------------- MODULE peterson_lock ---------------------------

\***************************************************************************
\* Peterson's Lock was first formalised in   
\*                             
\* G.L. Peterson : Myths About the Mutual Exclusion Problem
\*
\* Peterson's algorithm is a concurrent algorithm for solving the problem of 
\* mutual exclusion that allows multiple processes to sgare a single resource without conflicts  
\* Several versions of the lock exist. This specification formally presents the version that works with 2 processes. 
\*                                                   
\***************************************************************************


EXTENDS Integers,TLAPS


VARIABLES turn,state,flag
vars == <<turn,state,flag>>
ProcSet == {0,1}
States == {"Start","RequestTurn","Waiting","CriticalSection"}

Not(i) == 1-i

\***************************************************************************
\* State Initialisation for the processes. 
\* At the start of the logical time, both the processes have their flags set to false and the turn can be 0 or 1. 
\* The initial process control points to 'Start' for all the processes
\***************************************************************************


Init == /\ flag = [i \in ProcSet |-> FALSE]
        /\ turn \in {0,1}
        /\ state = [i \in ProcSet |-> "Start"]


\***************************************************************************
\* When the process makes progress, the first step is to capture the flag. The process does this by setting its entry in the list of flags to TRUE. 
\* The process can then request its turn.
\***************************************************************************

SetFlag(p) == 
        /\ state[p] = "Start"
        /\ flag' = [flag EXCEPT ![p] = TRUE]
        /\ state' = [state EXCEPT ![p] = "RequestTurn"]
        /\ UNCHANGED <<turn>>
        
        
\***************************************************************************
\* After capturing the flag, the process indicates its intent by setting the turn to 
\* The processes then contend to get their turn. Process P1 gives the turn to P2 and vice a versa.
\* The process that comes first and has turn set to its entry then proceeds into the critical section.
\* The other process meanwhile enters the waiting state.
\***************************************************************************


SetTurn(p) == 
        /\ state[p] = "RequestTurn"
        /\ turn' = Not(p)
        /\ state' = [state EXCEPT ![p] = "Waiting"]
        /\ UNCHANGED <<flag>>

\***************************************************************************
\* In the waiting state, the process keeps checking for its turn. 
\* If it observes the turn set to its own process identifier or notices that the other process has 
\* given up the intent to move into the critical section by setting its flag to false, the waiting process enters the critical section.
\***************************************************************************
        
        
EnterCriticalSection(p) == 
        /\ state[p] = "Waiting"
        /\ (flag[Not(p)] = FALSE \/ turn = p)
        /\ state' = [state EXCEPT ![p] = "CriticalSection"]
        /\ UNCHANGED <<turn,flag>>


\***************************************************************************
\* After exiting the critical section, cleanup is performed where the process sets its flag to false. This lets other processes proceed.
\***************************************************************************
   

ExitCriticalSection(p) == 
        /\ state[p] = "CriticalSection"
        /\ flag' = [flag EXCEPT ![p] = FALSE]
        /\ state' = [state EXCEPT ![p] = "Start"]
        /\ UNCHANGED <<turn>>
        
         
Next == \E p \in ProcSet:
        \/ SetFlag(p)
        \/ SetTurn(p)
        \/ EnterCriticalSection(p)
        \/ ExitCriticalSection(p)
        
        
Spec == Init /\ [][Next]_vars

proc(self) ==
        \/ SetFlag(self)
        \/ SetTurn(self)
        \/ EnterCriticalSection(self)
        \/ ExitCriticalSection(self)


SpecWithFairness == Spec /\ WF_vars(Next) /\ \A p \in {0, 1} : WF_vars(SetFlag(p))

\***************************************************************************
\* The execution invariant assers the following:
\* `^ 
\* \begin{enumerate}
\*  \item   For all the processes, If the process has proceeded from the start state, it should have set its flag. 
\*  \item   If a process is in the critical section, then no other process shoudl be in the critical section
\*  \item   For any process that is waiting, the turn should be set to the process that is making progress. 
\* \end{enumerate}
\*  ^
\***************************************************************************
 

ExecutionInvariant == \A i \in ProcSet:
        /\ state[i] \in States \ {"Start"} => flag[i]
        /\ state[i] \in {"CriticalSection"} =>  /\ state[Not(i)] \notin {"CriticalSection"}
                                                /\ state[Not(i)] \in {"Waiting"} => turn = i

\***************************************************************************
\* The Type invariant assers the following:
\* `^ 
\* \begin{enumerate}
\*  \item   The state for any process shoule be one of the predefined states i.e. Start, Set Flag, Set Turn, Waiting or Critical section. 
\*  \item   Turn should only be set to valid process identifiers.
\*  \item   Flag should be set to either TRUE or FALSE. 
\* \end{enumerate}
\*  ^
\***************************************************************************
 
TypeInvariant == /\ state \in [{0,1} -> States]
                 /\ turn \in {0,1}
                 /\ flag \in [{0,1} -> {TRUE,FALSE}]
                 
\***************************************************************************
\* The mutual exclusion property ensures that no 2 processes enter the critical section at the same time.
\* For every possible execution of the specification, in every state, the property should hold true.
\***************************************************************************

MutualExclusion == ~(state[0] = "CriticalSection" /\ state[1] = "CriticalSection")

Inv == ExecutionInvariant /\ TypeInvariant



\***************************************************************************
\* Formal proof that Petersons algorithm solves mutual exclusion.
\*
\*
\* The proof is a standard invariance proof that assers that any step of the algorithm
\* starting in a state in which an invariant is true leaves the invariant true.
\*
\*  <1>1 Asserts that the Execution and Type Invariants are true in the Initial state. The proof for this step is straightforward.
\*
\*  <1>3 Asserts that the Execution and Type Invariants together imply Mutual exclusion. This step is proved using the results from step <1>2.
\*
\*  <1>2 Asserts that if the Invariants are true and any process makes progress,the invariants still hold true in the next state.
\***************************************************************************



THEOREM Spec => []MutualExclusion
PROOF 
    <1>1. Init => Inv
        BY DEFS Init, Inv, TypeInvariant, ExecutionInvariant, vars,States,ProcSet
        
        
    <1>2. Inv /\ [Next]_vars => Inv'
        <2>1. SUFFICES ASSUME Inv, Next PROVE Inv' 
            BY DEFS ExecutionInvariant,TypeInvariant,Inv,vars
        <2>2. TypeInvariant'
            BY <2>1 
            DEFS Inv, TypeInvariant, Next, proc, Not, States, ProcSet, 
            SetFlag, SetTurn, EnterCriticalSection, ExitCriticalSection
\***************************************************************************
\* For this part of the proof, we expand the invariants on randomly chosen processes from the process identifiers.
\* The two cases possible are <3>3 and <3>4
\***************************************************************************
        <2>3. ExecutionInvariant'
            <3>1. SUFFICES ASSUME NEW j \in ProcSet PROVE ExecutionInvariant!(j)' BY 
            DEF ExecutionInvariant,ProcSet
            <3>2. PICK i \in ProcSet : proc(i)
                BY  <2>1 
                DEF Next,ProcSet,proc, SetFlag, SetTurn, 
                EnterCriticalSection, ExitCriticalSection
\***************************************************************************
\* If we select the same process and check the execution invariants, the proof is obvious
\***************************************************************************
            <3>3. CASE i=j
                BY <2>1,<3>2,<3>3 
                DEFS ExecutionInvariant, TypeInvariant, Inv, proc, 
                Not,ProcSet, SetFlag, SetTurn, EnterCriticalSection, ExitCriticalSection
\***************************************************************************
\* If we select different processes and check the execution invariants, The invariants are expanded and the proof is obvious.
\***************************************************************************
            <3>4. CASE i#j
                BY <2>1,<3>2,<3>3 
                DEFS ExecutionInvariant, TypeInvariant, Inv, proc, Not,ProcSet,
                 SetFlag, SetTurn, EnterCriticalSection, ExitCriticalSection
            <3>. QED BY <3>3,<3>4
\***************************************************************************
\* The subparts of the above proof are collected in the QED step to prove Type
\* invariance and Execution Invariance after every step taken according to the next state predicate
\***************************************************************************
        <2>4. QED BY <2>2,<2>3 DEF Inv
        
        
    <1>3. Inv => MutualExclusion  
        BY DEF Inv, MutualExclusion,ProcSet,Not,ExecutionInvariant,TypeInvariant
    <1>4. QED BY <1>1,<1>2,<1>3,PTL 
    DEF MutualExclusion,Spec,ExecutionInvariant, TypeInvariant, Inv, 
    proc, Not,ProcSet, SetFlag, SetTurn, EnterCriticalSection, ExitCriticalSection
    
=============================================================================
\* Modification History
\* Last modified Thu Dec 10 00:21:33 CET 2020 by pandey
\* Last modified Wed Nov 11 14:06:41 CET 2020 by ayushpandey
\* Created Tue Nov 03 21:42:32 CET 2020 by ayushpandey
