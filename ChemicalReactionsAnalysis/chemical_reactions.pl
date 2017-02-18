
% ---------- Declarations ---------- %

% substance(X) 	--> The name of a substance that can be used in the experiment. %
% canreact(X,Y) --> Defines a pair of substances that can react. %
% given(X) 	--> The substance is added to the mix when we start the experiment. %
% produced(X,N) --> The substance X is in the mix at timestep N. %
% normal(X,Y,N) --> The substance X reacts with the substance Y at timestep N, in the normal(usual) way. %
% abnormal(X,Y,N) 	 --> The substance X reacts with the substance Y at timestep N, in an abnormal(unusual) way. %
% imperfect_left(X,Y,N)  --> The substance X reacts with the substance Y at timestep N, and a quantity of X persists in the next timestep. %
% imperfect_right(X,Y,N) --> The substance X reacts with the substance Y at timestep N, and a quantity of Y persists in the next timestep. %

:- dynamic substance/1, can_react/2, given/1, produced/2, normal/3, abnormal/3, imperfect_left/3, imperfect_right/3,
   ic/0, abducible_predicate/1.


% ---------- Theory ---------- %

% Define the available substances. %
substance(subs1).
substance(subs2).
substance(subs3).
substance(subs4).
substance(subs5).
substance(subs6).
substance(subs7).
substance(subs8).
substance(subs9).
substance(subs10).
substance(subs0001).
substance(subs0002).
substance(subs0003).
substance(subs0004).
substance(subs0005).

% Define their possible reactions. %
can_react(subs1,subs2).
can_react(subs1,subs7).
can_react(subs1,subs9).
can_react(subs5,subs10).
can_react(subs7,subs8).
can_react(subs6,subs7).
can_react(subs0002,subs4).
can_react(subs0003,subs4).

% Define which substances are initially added to the mix.
given(subs1).
given(subs2).
given(subs6).
given(subs7).
given(subs8).

% If a substance is added to the mix, then it is present(produced) at timestep 1. %
produced(X,1) :- given(X).

% Define how a substance continues to be present(produced) in the case of an imperfect reaction. %
produced(X,M) :- M>1, N is M-1, substance(X), substance(Y), can_react(X,Y), imperfect_left(X,Y,N).
produced(Y,M) :- M>1, N is M-1, substance(X), substance(Y), can_react(X,Y), imperfect_right(X,Y,N).

% Define the products of all possible reactions. %
% There are 2 cases for a reaction, it can be normal or abnormal. %
% In the abnormal case the produced substances will differ from those of in the normal case. %

produced(subs3,M) :- M is N+1, produced(subs1,N), produced(subs2,N), normal(subs1,subs2,N).
produced(subs4,M) :- M is N+1, produced(subs1,N), produced(subs2,N), normal(subs1, subs2,N).

produced(subs4,M) :- M is N+1, produced(subs1,N), produced(subs2,N), abnormal(subs1,subs2,N).
produced(subs5,M) :- M is N+1, produced(subs1,N), produced(subs2,N), abnormal(subs1,subs2,N).

produced(subs9,M) :- M is N+1,  produced(subs7,N), produced(subs8,N), normal(subs7,subs8,N).

produced(subs10,M) :- M is N+1,  produced(subs7,N), produced(subs8,N), abnormal(subs7,subs8,N).

produced(subs0001,M) :- M is N+1, produced(subs5,N), produced(subs10,N), normal(subs5,subs10,N).
produced(subs0002,M) :- M is N+1, produced(subs1,N), produced(subs7,N), normal(subs1,subs7,N).
produced(subs0002,M) :- M is N+1, produced(subs6,N), produced(subs7,N), normal(subs6,subs7,N).

produced(subs0003,M) :- M is N+1, produced(subs0002,N), produced(subs4,N), normal(subs0002,subs4,N).

produced(subs0004,M) :- M is N+1, produced(subs1,N), produced(subs9,N), abnormal(subs1,subs9,N).

produced(subs0005,M) :- M is N+1, produced(subs0003,N), produced(subs4,N), abnormal(subs0003,subs4,N).


% ---------- Integrity Constraints ---------- %

% We cannot have a normal reaction between X and Y at N and, at the same time, substance X (or Y) not available at that timestep. %
ic :- normal(X,Y,N), not(produced(X,N)).
ic :- normal(X,Y,N), not(produced(Y,N)).

% We cannot have an abnormal reaction between X and Y at N and at the same time substance X (or Y) not available at that timestep. %
ic :- abnormal(X,Y,N), not(produced(X,N)).
ic :- abnormal(X,Y,N), not(produced(Y,N)).

% We cannot have imperfect_left (or right) if neither a normal nor an abnormal reaction is made. %
ic :- not(normal(X,Y,N)), not(abnormal(X,Y,N)), imperfect_left(X,Y,N).
ic :- not(normal(X,Y,N)), not(abnormal(X,Y,N)), imperfect_right(X,Y,N).

% We cannot have both a normal and an abnormal reaction between the same 2 substances at the same timestep. %
ic :- normal(X,Y,N), abnormal(X,Y,N).

% We cannot have both an imperfect_left and an imperfect_right reaction between the same 2 substances at the same timestep. %
ic :- imperfect_left(X,Y,N), imperfect_right(X,Y,N).

% We cannot have 2 reactions that share a same substance and the same timestep. % 
ic :- normal(X,Y,N), normal(X,Z,N), not(Y==Z).
ic :- normal(X,Y,N), normal(Z,Y,N), not(X==Z).
ic :- normal(X,Y,N), abnormal(X,Z,N), not(Y==Z).
ic :- normal(X,Y,N), abnormal(Z,Y,N), not(X==Z).
ic :- abnormal(X,Y,N), abnormal(X,Z,N), not(Y==Z).
ic :- abnormal(X,Y,N), abnormal(Z,Y,N), not(X==Z).



% ---------- Abducible predicates ---------- %

% We are allowed to make hypotheses about the way reactions happened. %
% Any possible reaction (from the set of reactions that led to the final position) could have been %
% normal, abnormal, imperfect_left, imperfect_right, or any combination of those types (if allowed by our constraints). %

abducible_predicate(normal).
abducible_predicate(abnormal).
abducible_predicate(imperfect_left).
abducible_predicate(imperfect_right).


% ---------- Tests ---------- %

% Substances produced in the second timestep. %

% eval([produced(subs4, 2)],[],Delta). %
% eval([produced(subs4, 2), produced(subs9, 2)], [], Delta). %
% eval([produced(subs0002, 2)], [], Delta). %
% eval([produced(subs0002, 2), produced(subs1, 2)], [], Delta). %
% eval([produced(subs0002, 2), produced(subs4, 2)], [], Delta). %

% Substances produced in the third timestep. %

% eval([produced(subs0001, 3), produced(subs1, 2)], [], Delta). %
% eval([produced(subs0003, 3)], [], Delta). %
% eval([produced(subs4, 3)], [], Delta). %
% eval([produced(subs0004, 3)], [], Delta). %


