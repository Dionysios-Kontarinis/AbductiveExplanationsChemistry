% xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx %
%  ProLogICA v2.7 (Jan 2009)					      %
% =================================================================== %
%  Oliver Ray -  oray@cs.bris.ac.uk     			      %
% xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx %

% NOTE THAT PROLOGICA IS NOW A LEGACY SYSTEM
% A REPLACEMNT SYSTEM XHAIL IS COMING SOON
% PLEASE SEE THE FOLLOWING ARTICLE
% Nonmonotonic Abductive Inductive Learning
% O. Ray. Journal of Applied Logic, 2009.

% intendended for Sicstus Prolog 3.12.2
% provisional support for SWI Prolog 5.6.34
% replace multi-line /* ... */ comments by %
% rename succ to suc
% rename get_time (and set_ show_ ) to getTime
% redefine retract_dynamic
% remove built-ins from closed_predicate
% remove module persist
% comment out deduce
% note that help screen does not work for SWI
% work around unknown predicate handlers at top of initialise
% also prep previous dynamic predicates ics/0,icu/0.
% modify built_in to exclude negative literals (not X)
% de-sensitise instantiation exception for SWI
% reverse concat in demo_fragment to give more Prolog-like selection
% disable frag for the same reason

% path('C:\\Users\\oliver\\RESEARCH\\Software\\PROLOGICA\\version6').

% ================================================================ %
%                TOP-LEVEL                                         %
% ================================================================ %

eval(Goals,FinalHyp) :- eval(Goals,[],FinalHyp).

demo(Goals,FinalHyp) :- demo(Goals,[],FinalHyp).

eval(Goals,InitHyp,FinalHyp) :- 
  findall(Delta,demo(Goals,InitHyp,Delta),Deltas),
  sortn(Deltas,InterHyps),
  minimalise(InterHyps,FinalHyps),
  mem(FinalHyp,FinalHyps).
  
demo(InitGoals,InitHyp,FinalHyp) :- 
  pre_process(InitGoals,InitHyp,MaxAbDepth),
  demo(InitGoals,InitHyp,[],InterHyp,InterCon,false,MaxAbDepth),
  post_process(InterHyp,InterCon,FinalHyp).
   
% ================================================================ %
%              ABDUCTIVE PHASE                                     %
% ================================================================ %

demo([],Hyp,Con,Hyp,Con,_,_) :- !.      
  
demo(Goals,InitHyp,InitCon,FinalHyp,FinalCon,Flound,AbDepth) :- 
  fragments(Goals,Frags),
  demo_fragments(Frags,InitHyp,InitCon,FinalHyp,FinalCon,Flound,AbDepth).
   
% ================================================================ %

demo_fragments([],InitHyp,InitCon,InitHyp,InitCon,_,_) :- !.
  
demo_fragments([Frag|Frags],InitHyp,InitCon,FinalHyp,FinalCon,Flound,AbDepth):-
  reduceBound(AbDepth,NewAbDepth),
  ab_select(Frag,InitHyp,InitCon,Goal,Prop,Goals),
  
  print_stuff(Goal,Goals,NewAbDepth),
  
  catch(demo_fragment(Prop,Goal,Goals,InitHyp,InitCon,InterHyp,InterCon,Flound,NewAbDepth),
  pureAbFragEx(NewGoal,NewGoals),(Goal=NewGoal,Goals=NewGoals,InterHyp=InitHyp,InterCon=InitCon)),
  demo_fragments(Frags,InterHyp,InterCon,FinalHyp,FinalCon,Flound,NewAbDepth).

print_stuff(Goal,Goals,NewAbDepth) :-
  option(max_ab_depth,M),D is M-NewAbDepth,spaces(D,S),name(T,S),
  (option(debug_info)->write_all([D,': ',T,'show ',Goal,' remain ',Goals,'\n']);true).



  
% ================================================================ %

% can throw after ground goal
demo_fragment((P,1,T,A,B,C),Goal,InitGoals,InitHyp,InitCon,FinalHyp,FinalCon,Flound,AbDepth) :-!,
  demo_one((P,1,T,A,B,C),Goal,MoreGoals,InitHyp,InitCon,InterHyp,InterCon,Flound,AbDepth),
  concat(MoreGoals,InitGoals,FinalGoals), %%%
  demo(FinalGoals,InterHyp,InterCon,FinalHyp,FinalCon,Flound,AbDepth),
  (option(pure_frag_ex)->(InitHyp=FinalHyp->throw(pureAbFragEx(Goal,InitGoals));true);true).

% not safe to throw in non-ground case as context my be lost
% i.e. may cut alternative bindings to goal variables
demo_fragment((P,0,T,A,B,C),Goal,InitGoals,InitHyp,InitCon,FinalHyp,FinalCon,Flound,AbDepth) :-
  demo_one((P,0,T,A,B,C),Goal,MoreGoals,InitHyp,InitCon,InterHyp,InterCon,Flound,AbDepth),
  concat(MoreGoals,InitGoals,FinalGoals), %%%
  demo(FinalGoals,InterHyp,InterCon,FinalHyp,FinalCon,Flound,AbDepth).

% ================================================================ %

ab_select([],_,_,success,_,[]):-!.

ab_select(Lits,Hyp,Con,Lit,Prop,OtherLits) :- 
	sel(Lits,Lit,OtherLits),
	ab_properties(Lit,Hyp,Con,Prop),
	non_floundered(Prop),
	!.
		
% ================================================================ %

% floundered (non-ground) %
demo_one(_,flounder,[],Hyp,Con,Hyp,Con,Flound,_) :- !,Flound=true.

% execute built-in %
demo_one(_,Lit,[],Hyp,Con,Hyp,Con,_,_) :- built_in(Lit),!,Lit.

% otherwise succeeded %
demo_one(Prop,_,[],Hyp,Con,Hyp,Con,_,_) :- succeeded(Prop),!.

% successful query %
demo_one(_,success,[],Hyp,Con,Hyp,Con,_,_) :- !.

% special demon (i.e. "demo") predicate (needed to overcome Sicstus intervention) %
demo_one((1,_,(1,0,0),(0,0,0)),demon(Call),Call,Hyp,Con,Hyp,Con,_,_) :- !.

% special atleast predicate: atleast(N,Calls) means ensure the success of at least N of the Calls
% to ensure minimality, first check for pure calls %
demo_one((1,1,(1,0,0),(0,0,0)),atleast(N,Calls),MoreGoals,Hyp,Con,Hyp,Con,Flound,AbDepth) :- !,
  (N=<0 -> MoreGoals=[] ; % optimisation to avoid unnecessarily partitioning if no goals left to succeed
  length(Calls,C), C>=N,
  partition(Calls,AlreadySucceeded,NotYetSucceeded,Call,demo([Call],Hyp,Con,Hyp,Con,Flound,AbDepth)),
  length(AlreadySucceeded,M), K is ((N-M)-1),
  (K<0 -> MoreGoals=[] ; 
    mem(OneCall,NotYetSucceeded,OtherCalls),
    length(OtherCalls,J),K=<J, % optimisation to avoid unnecessarily runnning demo if others cannot suffice
    MoreGoals=[OneCall,atleast(K,OtherCalls)])).
            
% Attempt Pure Computation (Only if ground! Otherwise, altermatives may avoid floundering elsewhere) %
demo_one((1,1,(1,0,0),(0,0,0)),SelectedLit,[],Hyp,Con,Hyp,Con,Flound,AbDepth) :- 
  option(require_minimal),
  %option(max_ab_depth,M),D is M-AbDepth,spaces(D,S),name(T,S),
  %(option(debug_info)->write_all([T,'  minimal[',SelectedLit,']\n']);true),
  clause_list(SelectedLit,Body),
  demo(Body,Hyp,Con,Hyp,Con,Flound,AbDepth),!.
        
% Attempt ImPure Computation %
demo_one((1,_,(1,0,0),(0,0,0)),SelectedLit,Body,Hyp,Con,Hyp,Con,_,_) :- !,
  %option(max_ab_depth,M),D is M-AbDepth,spaces(D,S),name(T,S),
  %(option(debug_info)->write_all([T,'  non-minimal[',SelectedLit,']\n']);true),
  clause_list(SelectedLit,Body).
 
% non-assumed negative ground program %
% assume, providing can falsify complement
demo_one((0,1,(1,0,0),(0,0,0)),SelectedLit,[],InitHyp,InitCon,FinalHyp,FinalCon,Flound,AbDepth) :- !,
  add_hypothesis(SelectedLit,InitHyp,InterHyp),
  complement(SelectedLit,Comp),
  option(max_con_depth,MaxConDepth),
  demo_failure([[Comp]],InterHyp,InitCon,FinalHyp,FinalCon,Flound,AbDepth,MaxConDepth).

% negative built_in %
demo_one((0,_,(0,0,1),(0,0,0)),SelectedLit,[],InitHyp,InitCon,FinalHyp,FinalCon,Flound,AbDepth) :- !,
  complement(SelectedLit,Comp),
  option(max_con_depth,MaxConDepth),
  demo_failure([[Comp]],InitHyp,InitCon,FinalHyp,FinalCon,Flound,AbDepth,MaxConDepth).

% already know that literal is consistent with facts in Con

% non-assumed negative ground abducible %
demo_one((0,1,(0,1,0),(0,0,0)),SelectedLit,[],InitHyp,Con,FinalHyp,Con,_,_) :- !,
  add_hypothesis(SelectedLit,InitHyp,FinalHyp).

% non-assumed positive Ground abducible%
demo_one((1,1,(0,1,0),(0,0,0)),SelectedLit,[],InitHyp,InitCon,FinalHyp,FinalCon,Flound,AbDepth) :- !,
  add_hypothesis(SelectedLit,InitHyp,InterHyp),
  demo_fail_ICS(SelectedLit,InterHyp,InitCon,FinalHyp,FinalCon,Flound,AbDepth).


% ================================================================ %
%              CONSISTENCY PHASE                                   %
% ================================================================ %

demo_fail_ICS(Lit,InitHyp,InitCon,FinalHyp,FinalCon,Flound,AbDepth) :-
  findall(Residue,(clause_list(ic,IC),resolve(Lit,IC,Residue)),NormalICs),
  findall(Residue,(clause_list(icu,IC),resolve(Lit,IC,Residue)),StaticICs),
  findall(Residue,(mem(IC,InitCon),resolve(Lit,IC,Residue)),DynamicICs),
  concat_all([NormalICs,StaticICs,DynamicICs],ICs),option(max_con_depth,MaxConDepth),
  demo_failure(ICs,InitHyp,InitCon,FinalHyp,FinalCon,Flound,AbDepth,MaxConDepth).

% ================================================================ %

demo_failure([],Hyp,Con,Hyp,Con,_,_,_) :- !.

demo_failure([IC|ICs],InitHyp,InitCon,FinalHyp,FinalCon,Flound,AbDepth,ConDepth) :- 
  reduceBound(ConDepth,NewConDepth),
  catch(demo_failure_leaf(IC,InitHyp,InitCon,InterHyp,InterCon,Flound,AbDepth,NewConDepth),
  pureConFragEx,(InterHyp=InitHyp,InterCon=InitCon)),
  demo_failure(ICs,InterHyp,InterCon,FinalHyp,FinalCon,Flound,AbDepth,NewConDepth).

% ================================================================ %
    
demo_failure_leaf(IC,InitHyp,InitCon,InitHyp,InitCon,Flound,AbDepth,ConDepth) :-
  option(require_minimal),
  catch((fragment(IC,Frag),
  demo_failure_fragment(Frag,InitHyp,InitCon,InitHyp,InitCon,Flound,AbDepth,ConDepth)),
  pureConLitEx,true),!,(option(pure_frag_ex)->throw(pureConFragEx);true).

demo_failure_leaf(IC,InitHyp,InitCon,InterHyp,InterCon,Flound,AbDepth,ConDepth) :-
  catch((fragment(IC,Frag),
  demo_failure_fragment(Frag,InitHyp,InitCon,InterHyp,InterCon,Flound,AbDepth,ConDepth)),
  pureConLitEx,(InterHyp=InitHyp,InterCon=InitCon)),
  (option(pure_frag_ex)->(InterHyp=InitHyp->throw(pureConFragEx);true);true).
    
% ================================================================ %
    
demo_failure_fragment(Frag,InitHyp,InitCon,InterHyp,InterCon,Flound,AbDepth,ConDepth) :-
  con_select(Frag,InitHyp,InitCon,SelectedLit,Prop,OtherLits),
  option(max_ab_depth,M),option(max_con_depth,N),D is M-AbDepth,C is N-ConDepth,
  spaces(D,S),name(T,S),spaces(C,U),name(V,U),
  (option(debug_info)->write_all([D,': ',T,C,V,'fail ',SelectedLit,' remain ',OtherLits,'\n']);true),
  demo_failure_on_literal(Prop,SelectedLit,OtherLits,
                          InitHyp,InitCon,InterHyp,InterCon,Flound,AbDepth,ConDepth),
  (option(pure_frag_ex)->(InterHyp=InitHyp->throw(pureConLitEx);true);true).

% ================================================================ %

con_select(IC,Hyp,Con,Lit,Prop,OtherLits):-
  con_partition(IC,Hyp,Con,B,C,D,E,F,G),
  concat(B,C,BC),concat(E,G,EG),
  con_select_each(BC,D,EG,F,Lit,Prop,OtherLits).
    
con_partition([],_,_,[],[],[],[],[],[]):-!.

con_partition([Lit|OtherLits],Hyp,Con,B,C,D,E,F,G):-
  con_properties(Lit,Hyp,Con,Prop),
  con_partition(OtherLits,Hyp,Con,Bs,Cs,Ds,Es,Fs,Gs),
  (Bs=[(success,_)] ->              % already succeeded
    B=Bs,C=Cs,D=Ds,E=Es,F=Fs,G=Gs;          
  (succeeded(Prop) ->               % remove successful lit
    B=Bs,C=Cs,D=Ds,E=Es,F=Fs,G=Gs;          
  (failed(Prop) ->              % succeed if lit failed 
    B=[(success,_)],C=[],D=[],E=[],F=[],G=[];   
  (floundered(Prop),abducible(Lit) ->       % add flound abd to G
    B=Bs,C=Cs,D=Ds,E=Es,F=Fs,G=[(Lit,Prop)|Gs]; 
  (floundered(Prop) ->              % add flound non-abd to F
    B=Bs,C=Cs,D=Ds,E=Es,F=[(Lit,Prop)|Fs],G=Gs;
  (closed(Lit),grounded(Prop) ->        % add closed gnd lit to B
    B=[(Lit,Prop)|Bs],C=Cs,D=Ds,E=Es,F=Fs,G=Gs;
  (closed(Lit) ->               % add closed non-gnd lit to C
    B=Bs,C=[(Lit,Prop)|Cs],D=Ds,E=Es,F=Fs,G=Gs;
  (grounded(Prop) ->                % add open gnd lit to D
    B=Bs,C=Cs,D=[(Lit,Prop)|Ds],E=Es,F=Fs,G=Gs;
  % else %                    % add open non-gnd lit to E
    B=Bs,C=Cs,D=Ds,E=[(Lit,Prop)|Es],F=Fs,G=Gs
  )))))))).

% all lits floundered %
con_select_each([],[],[],[_F|_Fs],flounder,_,[]):-!.

% closed lit (first gnd, then non-gnd) %
con_select_each([(Lit,Prop)|Cs],D,E,F,Lit,Prop,OtherLits):- !,
  join_all([Cs,D,E,F],OtherLits).

con_select_each([],D,E,F,Lit,Prop,OtherLits):- 
  \+option(gnd_lit_sep),!,
  concat(D,E,LitProps),
  sel(LitProps,(Lit,Prop),OtherLitProps),
  join_all([OtherLitProps,F],OtherLits).

% open gnd %
con_select_each([],[D|Ds],_E,_F,Lit,Prop,[]):-
  sel([D|Ds],(Lit,Prop),_MoreLits).

% open non-gnd %
con_select_each([],_D,[E|Es],F,Lit,Prop,OtherLits):-
  sel([E|Es],(Lit,Prop),MoreLits),
  join_all([MoreLits,F],OtherLits).

% ================================================================ %

% abort if literal declared consistent %

demo_failure_on_literal(_Prop,Lit,OtherLits,
        InitHyp,InitCon,InterHyp,InterCon,Flound,AbDepth,ConDepth):- 
	ground(Lit),consistent(Lit),!,
	format('\n***could not fail ~q as it is declared consistent***\n\n',[Lit]),
	(closed(Lit)->demo_failure_fragment(OtherLits,
	InitHyp,InitCon,InterHyp,InterCon,Flound,AbDepth,ConDepth)).

% floundered %
demo_failure_on_literal(_,flounder,_,
        InitHyp,InitCon,InitHyp,InitCon,Flound,_,_) :- !,Flound=true.

% successful %
demo_failure_on_literal(_,success,_,InitHyp,InitCon,
        InitHyp,InitCon,_,_,_) :- !.

% negative %
demo_failure_on_literal((0,1,(_,_,_),(0,0,0)),SelectedLit,_,InitHyp,InitCon,
        InterHyp,InterCon,Flound,AbDepth,_ConDepth) :- !,
  complement(SelectedLit,Comp),
  demo([Comp],InitHyp,InitCon,InterHyp,InterCon,Flound,AbDepth).

% special  %
demo_failure_on_literal((1,1,(1,0,0),(0,0,0)),demon(Call),_,InitHyp,InitCon,FinalHyp,FinalCon,Flound,AbDepth,ConDepth) :- !,
    demo_failure([[Call]],InitHyp,InitCon,FinalHyp,FinalCon,Flound,AbDepth,ConDepth).

% special  %
demo_failure_on_literal((1,_,(1,0,0),(0,0,0)),atleast(N,Calls),_,InitHyp,InitCon,FinalHyp,FinalCon,Flound,AbDepth,ConDepth) :- !,
  N>0,length(Calls,C),
  (C<N -> true ; 
    partition(Calls,_AlreadyFailed,NotYetFailed,Call,demo_failure([[Call]],InitHyp,InitCon,InitHyp,InitCon,Flound,AbDepth,ConDepth)),
    (NotYetFailed=[] -> true ;
      (NotYetFailed=[OneCall|OtherCalls],
        (
        (demo_failure([[OneCall]],InitHyp,InitCon,InterHyp,InterCon,Flound,AbDepth,ConDepth),
         demo_failure([[atleast(N,OtherCalls)]],InterHyp,InterCon,FinalHyp,FinalCon,Flound,AbDepth,ConDepth))
        ;
        (M is N-1,
         demo_failure([[atleast(M,OtherCalls)]],InitHyp,InitCon,FinalHyp,FinalCon,Flound,AbDepth,ConDepth))
        )
      )
    )
  ).

% positive program %
demo_failure_on_literal((1,_,(1,0,0),(0,0,0)),SelectedLit,OtherLits,
        InitHyp,InitCon,InterHyp,InterCon,Flound,AbDepth,ConDepth):-!,
  findall(IC,(clause_list(SelectedLit,Body),concat(Body,OtherLits,IC)),ICs),
  demo_failure(ICs,InitHyp,InitCon,InterHyp,InterCon,Flound,AbDepth,ConDepth).

% positive floundered abducible %
demo_failure_on_literal((1,0,(0,1,0),(0,0,1)),SelectedLit,OtherLits,
        InitHyp,InitCon,InterHyp,InterCon,Flound,AbDepth,ConDepth) :- !,
  findall(OtherLits,mem(SelectedLit,InitHyp),Residues),
  demo_failure(Residues,InitHyp,InitCon,InterHyp,Con,Flound,AbDepth,ConDepth),
  concat([[SelectedLit|OtherLits]],Con,InterCon).

% non-assumed positive ground abducible %
demo_failure_on_literal((1,1,(0,1,0),(0,0,0)),SelectedLit,_RestOfLiterals,
        InitHyp,InitCon,InterHyp,InitCon,_,_,_) :- !,
  complement(SelectedLit,Comp),
  add_hypothesis(Comp,InitHyp,InterHyp).


% ================================================================ %
%                  LOW-LEVEL PREDICATES                          
% ================================================================ %

%is_list([]).
%is_list([_|_]).

subset(X,Y) :- \+ (mem(E,X),\+ mem(E,Y)).
supset(X,Y) :- \+ (mem(E,Y),\+ mem(E,X)).

mem(X,[X|_Y]).          % mem(-member,+list)
mem(X,[_Z|Y]):-mem(X,Y).

mem(X,[X|Y],Y).         % mem(-member,+list,-following members)
mem(X,[_|Y],Z):-mem(X,Y,Z). 

in(X,[X|_Y]):-!.        % in(+element,+list)
in(X,[_Z|Y]):-in(X,Y).

elem(X,[Y|_Z]):-X==Y,!.     % in(+element,+list), no binding
elem(X,[_Z|Y]):-elem(X,Y).

concat([],U,U).
concat([X|Y],U,[X|V]):-concat(Y,U,V).

concat_all([],[]).
concat_all([H|T],X):-concat_all(T,Y),concat(H,Y,X).

sel([X|Y],X,Y).         % select one and return all the others
sel([Z|Y],X,[Z|Rest]):-sel(Y,X,Rest).

intersect([U|_V],[X|Y]):-elem(U,[X|Y]),!.
intersect([_U|V],[X|Y]):-intersect(V,[X|Y]).

%remove([1,1,2,3,4,5,6,7,2],[1,2,5],[3,4,6,7]).

remove([],_L,[]):-!.
remove([H|T],L,M):-elem(H,L),!,remove(T,L,M).
remove([H|T],L,[H|M]):-remove(T,L,M).

%insert([4,1,2,3],[3,4,5,2],[5,4,1,2,3])

insert(L,[],L):-!.
insert(L,[H|T],M):-elem(H,L),!,insert(L,T,M).
insert(L,[H|T],[H|M]):-insert(L,T,M).

partition([],[],[],_,_).

% can use \+ \+ in Test to discard bindings

partition([U|V],[U|X],Y,Elem,Test):-
  copy_term((Elem,Test),(NewElem,NewTest)),
  U=Elem,Test,!,
  partition(V,X,Y,NewElem,NewTest).

partition([U|V],X,[U|Y],Elem,Test):-
  partition(V,X,Y,Elem,Test).

transform([],[],_,_,_,_).

%Op connects In and Out; Vars are "universally quantified"
%ie bindings are committed for all members

transform([U|V],[X|Y],In,Out,Op,Vars):-
  copy_term((In,Out,Op,Vars),(NewIn,NewOut,NewOp,Vars)),
  In=U,Op,X=Out,
  transform(V,Y,NewIn,NewOut,NewOp,Vars).

transform(LIn,LOut,In,Out,Op):-transform(LIn,LOut,In,Out,Op,[]).

accumulate([],_,_,_,_,Result,Result).

accumulate([U|V],Elem,In,Out,Op,Acc,Result):-
  copy_term((Elem,In,Out,Op),(NewElem,NewIn,NewOut,NewOp)),
  copy_term(U,Elem),copy_term(Acc,In),Op,!,
  accumulate(V,NewElem,NewIn,NewOut,NewOp,Out,Result).
  
accumulate([],_,Acc,Acc).

accumulate([U|V],Prop,Acc,Result):-
  accumulate(V,Prop,Acc,InterResult),
  Call=..[Prop,U,InterResult,Result],
  Call,!.
  
find_all(P,S,C):-findall(P,C,S).

for_all(F,C) :- \+ (F, \+ C).

% ================================================================ %
                  
resolve(L1,[L1|ClauseList],ClauseList).
resolve(Literal,[L1|ClauseList],[L1|Resolvent]) :- resolve(Literal,ClauseList,Resolvent).

clause_list(Head,Body) :- clause(Head,Bod),body_to_list(Bod,Body).

body_to_list((X,Y),[X|Z]):-!,body_to_list(Y,Z).
body_to_list(true,[]):- !.
body_to_list(X,[X]).

list_to_body([X],X):-!.
list_to_body([],true):-!.
list_to_body([X|Y],(X,Z)):-list_to_body(Y,Z).

flatten([],[]):-!.

flatten([Term|Terms],TermList):-
  var(Term),!,
  flatten(Terms,ArgList),
  TermList=[Term|ArgList].

flatten([Term|Terms],TermList):-
  Term=..['$VAR'|_],!,
  flatten(Terms,ArgList),
  TermList=[Term|ArgList].

flatten([Term|Terms],TermList):-
  Term=..[Functor|Args],
  concat(Args,Terms,ArgTerms),
  flatten(ArgTerms,ArgList),
  TermList=[Functor|ArgList].

vars(Term,Vars) :-  
  flatten([Term],TermList),
  partition(TermList,Variables,_OtherTerms,Elem,var(Elem)),
  sort(Variables,Vars).

prefix(Pref,Pred,NewPred) :-
  name(Pred,PredName),
  name(Pref,PrefName),
  concat(PrefName,PredName,NewPredName),
  name(NewPred,NewPredName).

un_prefix(Pref,Pred,NewPred) :-
  name(Pred,PredName),
  name(Pref,PrefName),
  concat(PrefName,NewPredName,PredName),
  name(NewPred,NewPredName).

% ================================================================ %

% literal properties %
ab_properties(Lit,Hyp,Con,(P,G,T,S)) :-
  suc(is_positive(Lit),P),
  suc(ground(Lit),G),
  complement(Lit,Comp),
  (P=1->type(Lit,T);
  (P=0->type(Comp,T))),
  ab_status(Lit,Comp,Hyp,Con,P,G,T,S).

con_properties(Lit,Hyp,Con,(P,G,T,S)) :-
  suc(is_positive(Lit),P),
  suc(ground(Lit),G),
  complement(Lit,Comp),
  (P=1->type(Lit,T);
  (P=0->type(Comp,T))),
  con_status(Lit,Comp,Hyp,Con,P,G,T,S).
  
% predicate type (of positive part) %            
type(Lit,T):-
  (built_in(Lit) ->T=(0,0,1);       % built-in
  (abducible(Lit)->T=(0,1,0);       % abducible
           T=(1,0,0))).     % program

% status of negative %
status(Lit,Comp,Hyp,Con,0,G,_T,S):-!,
  (G=0          ->S=(0,0,1);        % floundered
  (in(Lit,Hyp)  ->S=(1,0,0);        % entailed
  (in([Lit],Con)->S=(0,1,0);        % inconsistent
  (in(Comp,Hyp) ->S=(0,1,0);        % inconsistent
                  S=(0,0,0))))).    % assumable

% status of positive abducible %
status(Lit,Comp,Hyp,Con,1,G,(0,1,0),S):-!,
  (G=0          ->S=(0,0,1);        % floundered
  (in(Lit,Hyp)  ->S=(1,0,0);        % entailed
  (in([Lit],Con)->S=(0,1,0);        % inconsistent
  (in(Comp,Hyp) ->S=(0,1,0);        % inconsistent
                  S=(0,0,0))))).    % assumable

% status of positive program %
status(_Lit,_Comp,_Hyp,_Con,1,_G,(1,0,0),(0,0,0)).

% status of positive built-in (suc,fail,flounder) %
ab_status(A,B,C,D,E,F,G,H):-status(A,B,C,D,E,F,G,H).
ab_status(Lit,_Comp,_Hyp,_Con,1,_G,(0,0,1),S):-!,  
  telling(Out),
  tell('null'),
  copy_term(Lit,CopyLit),
  catch((suc(CopyLit,X),Y is 1-X,S=(X,Y,0)),_, 
    % in sicstus instantiation_error(_Goal,_Arg)
    (S=(0,0,1),told,tell(Out))),
  told,
  tell(Out).

% status of positive built-in (execute built-in but divert user output) %
con_status(A,B,C,D,E,F,G,H):-status(A,B,C,D,E,F,G,H).
con_status(Lit,_Comp,_Hyp,_Con,1,_G,(0,0,1),S):-!,  
  telling(Out),
  tell('null'),
  catch((suc(Lit,X),Y is 1-X,S=(X,Y,0)),_,
    % in sicscus instantiation_error(_Goal,_Arg),
    S=(0,0,1)),
  told,
  tell(Out),
  true.


% concatenate removing properties from first list %
join([],Lits,Lits).
join([(Lit,_Prop)|LPs],Lits,[Lit|MoreLits]) :- join(LPs,Lits,MoreLits).

% join list of property-lists %
join_all([],[]):-!.
join_all([H|T],Lits):-join_all(T,SomeLits),join(H,SomeLits,Lits).

is_positive(SelectedLit) :- \+ is_negative(SelectedLit).
is_negative(SelectedLit) :- SelectedLit= not(_OtherLit).

complement(not(Comp),Comp):-!.
complement(Lit,not(Lit)).

abducible(Atom) :- 
  get_predicate_name(Atom,PredicateName),
  abducible_predicate(PredicateName).

get_predicate_name(Atom,PredicateName) :- 
  (Atom)=..[PredicateName|_Args].

built_in(X):-
  functor(X,Functor,Arity),
  \+ Functor=not,
  length(Args,Arity),
  Y=..[Functor|Args],
  predicate_property(Y,built_in).

% ground %
grounded((_,1,(_,_,_),(_,_,_))).
non_grounded((_,0,(_,_,_),(_,_,_))).

% floundered abducible or negative or built-in %
floundered((_,_,(_,_,_),(0,0,1))).
non_floundered((_,_,(_,_,_),(_,_,0))).

% (failed (positive) built-in) or (inconsistent negative or abducible)%
failed((_,_,(_,_,_),(0,1,0))).
non_failed((_,_,(_,_,_),(_,0,_))).

% assumed (abducible or negative); or (successful built-in) %
succeeded((_,_,(_,_,_),(1,0,0))).
non_succeeded((_,_,(_,_,_),(0,_,_))).

% ================================================================ %

merge_all(X,Z):-
  merge_first(X,Y),!,merge_all(Y,Z).

merge_all(X,X).

merge_first([H|T],HT):-
  merge(H,T,HT),!.
  
merge_first([H|T],[H|HT]):-
  merge_first(T,HT).
  
merge((X,VX),[(Y,VY)|YS],[(Z,VZ)|YS]):-
  intersect(VX,VY),!,
  concat(X,Y,UZ),sort(UZ,Z),
  concat(VX,VY,UVZ),sort(UVZ,VZ).
  
merge((X,VX),[(Y,VY)|YS],[(Y,VY)|ZS]):-
  merge((X,VX),YS,ZS).
  
fragment([Lit],[Lit]):-!. % just to speed things up!

fragment(Lits,Lits):- \+ option(shared_var_frags),!.
% all in same fragment if shared_var_frags disabled

fragment(Lits,Frag):-
  setof(([Lit],FreshVars),(mem(Lit,Lits),vars(Lit,FreshVars)),LitVarPairs),
  merge_all(LitVarPairs,FragmentPairs),mem((Frag,_),FragmentPairs).

fragments(Lits,Frags):-
  bagof(Frag,fragment(Lits,Frag),Frags).
   
% ================================================================ %

spaces(0,[]):-!.
spaces(N,[32|S]):-M is N-1, spaces(M,S).

suc(Call,1) :- Call,!.
suc(_Call,0).
    
%add to front
add_hypothesis(Hyp,ExpSoFar,[Hyp|ExpSoFar]) :- \+ option(order_abducibles),!.

% insert 
add_hypothesis(Hyp,[],[Hyp]):-!.
add_hypothesis(NewHyp,[OldHyp|OldHyps],[NewHyp,OldHyp|OldHyps]):-NewHyp@<OldHyp,!.
add_hypothesis(NewHyp,[OldHyp|OldHyps],[OldHyp|NewHyps]):-add_hypothesis(NewHyp,OldHyps,NewHyps).

reduceBound(0,_):-!,
  (option(show_bound_errors)->write('Depth Bound Exceeded\n'),fail).

reduceBound(Depth,NewDepth):-
  Depth\=0,NewDepth is Depth-1.

% display list %
write_line(X):-write(X),write('\n').

write_all([]).
write_all([H|T]):-write(H),write_all(T).

write_all_line([]).
write_all_line([H|T]):-write_line(H),write_all_line(T).

% remove negative lits %
remove_not([],[]):-!.
remove_not([not(_L)|M],N):-!,remove_not(M,N).
remove_not([L|M],[L|N]):-!,remove_not(M,N).

% remove negated abs whose non-proxy form is also abduced %
remove_ab(Init,Final) :- 
  findall(Lit,(mem(Lit,Init),remove_abs([Lit],[NewLit]),\+ (NewLit\=Lit,mem(NewLit,Init))),Inter),
  remove_abs(Inter,Final).

% remove ab_ prefix and not(ics) literal %
remove_abs([],[]):-!.
remove_abs([not(ics)|M],N):-!,remove_abs(M,N).
remove_abs([not(Lit)|M],[not(NewLit)|N]):-!,remove_abs([Lit|M],[NewLit|N]).
remove_abs([Lit|M],[NewLit|N]):-
  Lit=..[Pred|Args],
  name(Pred,[36,97,98,95|NewPredList]),!,
  name(NewPred,NewPredList),
  NewLit=..[NewPred|Args],
  remove_abs(M,N).
remove_abs([L|M],[L|N]):-remove_abs(M,N).

% timing %
setTime:-statistics(runtime,[_,_]).
getTime(Time):-statistics(runtime,[_,Time]).

sortn(L,M):-transform(L,P,I,O,(length(I,N),O=[N|I])),sort(P,Q),transform(Q,M,[_|E],E,!).
sortd(L,M):-transform(L,P,I,O,(length(I,N),K is -N,O=[K|I])),sort(P,Q),transform(Q,M,[_|E],E,!).

reverse(AZ,ZA):-reverse(AZ,[],ZA).
reverse([],Cs,Cs).
reverse([A|Bs],Cs,Ds):-reverse(Bs,[A|Cs],Ds).

% ================================================================ %

minimise(_,[],[]).
minimise(F,[G|Gs],[G|Hs]):-mem(E,F),\+ mem(E,G),!,minimise(F,Gs,Hs).
minimise(F,[_|Gs],Hs):-minimise(F,Gs,Hs).
minimalise([],[]).
minimalise([F|Fs],[F|Gs]):-minimise(F,Fs,Hs),minimalise(Hs,Gs).

% ================================================================ %

retract_dynamic :-
	predicate_property(Head,dynamic),
	\+ predicate_property(Head,built_in),
	Head =..[Pred|Vars],
	%write_line(Head),
	\+ mem(Pred,[initialised,fname,val]), 
	length(Vars,Len),
	%write_line(Pred),
	abolish(Pred,Len),
	fail;true.

advise(File):-tell(File),list,told.

list :-
  predicate_property(Head,dynamic),
  \+ predicate_property(Head,built_in),
  Head=..[Pred|Args],
  length(Args,_Len),
  listing(Pred),
  fail;true.

% ================================================================ %

initialise_closed_preds(ClosedPreds):-
  setof((HeadPred,BodyPreds),
    (setof(BodyPred,HeadAtom^BodyAtoms^BodyAtom^NonEmptyBodyAtoms^PosBodyAtom^
          (predicate_property(HeadAtom,dynamic),
           \+ predicate_property(HeadAtom,built_in),
           get_predicate_name(HeadAtom,HeadPred),
           clause_list(HeadAtom,BodyAtoms),
           (BodyAtoms=[]->NonEmptyBodyAtoms=[true];NonEmptyBodyAtoms=BodyAtoms),
           mem(BodyAtom,NonEmptyBodyAtoms),
           (is_positive(BodyAtom)->PosBodyAtom=BodyAtom;complement(BodyAtom,PosBodyAtom)),
           get_predicate_name(PosBodyAtom,BodyPred)),
           BodyPreds)),
     HeadBodyPreds),
  findall(AbduciblePred,abducible_predicate(AbduciblePred),AbduciblePreds),
  find_closed_preds(HeadBodyPreds,AbduciblePreds,ClosedPreds),
  findall(_,(mem(ClosedPred,ClosedPreds),asserta(closed_predicate(ClosedPred))),_).
    
find_closed_preds(HeadBodyPreds,[],ClosedPreds):-!,
  SysPreds=[abducible_predicate,closed_predicate,option,ic,icu,ics,fname,val],
  findall(ClosedPred,(mem((ClosedPred,_),HeadBodyPreds),\+ mem(ClosedPred,SysPreds)),ClosedPreds).
  
find_closed_preds(HeadBodyPreds,OpenPreds,ClosedPreds):-
  partition(HeadBodyPreds,OpenPredPairs,NewHeadBodyPreds,Elem,
           (Elem=(_,BodyPreds),intersect(BodyPreds,OpenPreds))),
  findall(NewOpenPred,mem((NewOpenPred,_),OpenPredPairs),NewOpenPreds),
  find_closed_preds(NewHeadBodyPreds,NewOpenPreds,ClosedPreds).
  
closed(Lit) :-
  get_predicate_name(Lit,Pred),
  (option(closed_pred_det)->closed_predicate(Pred);fail).

% ================================================================ %
     
initialise_ICs :-
  \+clause(ic,_)->true
  ;
  option(max_ic_unfold,N),(N=<0->true
  ;
  for_all((retract((ic:-IC)),body_to_list(IC,Bod),concat(Bod,[$],Bd),
  prefold(Bd,Bodies),mem(Body,Bodies)),unfold_ic(Body,N))).

% unfold each original abducible one step to recover renamed constraint

prefold([$|Bods],[Bods]):-!.
prefold([Bod|Bods],Bodies):-
  abducible_predicate(P),un_prefix('$ab_',P,Q),Bod=..[Q|_],!,
  findall(IC,(clause_list(Bod,Body),concat(Bods,Body,NewBods),prefold(NewBods,IC)),ICs),
  concat_all(ICs,Bodies).
prefold([Bod|Bods],Bodies):-
  concat(Bods,[Bod],Bds),
  prefold(Bds,Bodies).
 
unfold_ic([],_):-!,fail.  % violated a priori

unfold_ic(IC,_N):-  % contains abdicible -> icu
  mem(Lit,IC),
  abducible(Lit),!,
  list_to_body(IC,Bod),
  asserta((icu:-Bod)).
  
unfold_ic(IC,0):-!, % no luck -> ics
  list_to_body(IC,Bod),
  asserta((ics:-Bod)).
   
unfold_ic(IC,N):-   % unfold
  con_partition(IC,[],[],B,C,D,E,F,G),
  (B=[(success,_)]->true;
     (concat_all([B,C,D,E],LitProps),
     (sel(LitProps,(Lit,(1,_,(1,0,0),(0,0,0))),OtherLitProps)->
        (join_all([OtherLitProps,F,G],Lits),M is N-1,
         for_all((clause_list(Lit,Body),concat(Body,Lits,NewIC)),
           unfold_ic(NewIC,M)))
         ;
        (LitProps\=[]->unfold_ic(IC,0))))).

% ========================================================== %

initialise_auxiliary_preds(AuxPreds) :-
  \+abducible_predicate(_)->AuxPreds=[]
  ;
  option(max_ic_unfold,N),N=<0->AuxPreds=[]
  ;
  find_all(AuxPred,AuxPreds,
       (retract(abducible_predicate(AbPred)),
        current_predicate(AbPred,H),
        H=..[AbPred|Vars],
        prefix('$ab_',AbPred,AuxPred),
        prefix('$tp_',AbPred,TypPred),
        B=..[AuxPred|Vars],
        C=..[TypPred|Vars],
        asserta((H:-C,B)),
        asserta(abducible_predicate(AuxPred)))).
   
   
% ============================================================ %
%              MODE-H TRANSFORMATIONS	                       %
% ============================================================ %

transform_head_decs :- \+ modeh(_,_),! .%, write(['  NO HEAD DECS!']),write('\n').

transform_head_decs :-
	modeh(Recall,Scheme),
	!,
	Scheme=..[Pred|Args],
	prefix('$tp_',Pred,NewPred),
	transform_args(Args,NewArgs,NewCalls),
	length(Args,_Arity),
	Head=..[NewPred|NewArgs],
	body_to_list(Body,NewCalls),
	%write(['  replacing ',Scheme,' by ',(Head:-Body)]),write('\n'),
	retract(modeh(Recall,Scheme)),
	assert((Head:-Body)),
	assert(abducible_predicate(Pred)),
	transform_head_decs.


transform_args([],[],[]).	

transform_args([Arg|Args],NewArgs,NewCalls) :-
	transform_term(Arg,AnArg,SomeCalls),
	transform_args(Args,MoreArgs,MoreCalls),
	concat([AnArg],MoreArgs,NewArgs),
	concat(SomeCalls,MoreCalls,NewCalls).

	
transform_term(+(Type),Var,[TypeCall]) :- !, TypeCall=..[Type,Var].

transform_term(-(Type),Var,[TypeCall]) :- !, TypeCall=..[Type,Var].

transform_term(#(Type),Var,[TypeCall]) :- !, TypeCall=..[Type,Var].

transform_term(+,_,[]) :- !.

transform_term(-,_,[]) :- !.

transform_term(#,_,[]) :- !.

transform_term(Arg,AnArg,SomeCalls) :-
	Arg=..[Func|Args],
	transform_args(Args,NewArgs,SomeCalls),
	AnArg=..[Func|NewArgs].
	
	
% ========================================================== %

bad_clause((Head:-Bod)):-
    abducible_predicate(Pred),
    current_predicate(Pred,Head),
    clause(Head,Bod).

bad_ic((ic:-Bod)) :- 
    clause(ic,Bod),
    body_to_list(Bod,Body),
    \+ (in(Lit,Body), abducible(Lit)).

bad_clauses(ListOfBadClauses) :- 
    findall(BadClause,bad_clause(BadClause),ListOfBadClauses).

bad_ics(ListOfBadICs) :- 
    findall(BadIC,bad_ic(BadIC),ListOfBadICs).



% ============================================================ %
%              PRE/POST PROCESSING 
% ============================================================ %

:- nl.
:- write_line('***************************************').
:- write_line('* ProLogICA (v2.7) ALP interpreter    *').
:- write_line('* by Oliver Ray (Jan 2009 )           *').
:- write_line('* for Sicstus (3.12.2) & SWI (5.6.34) *').
:- write_line('* type "user_help" for help           *').
:- write_line('***************************************').
:- op(900,fy,[not,#]).
:- use_module(library(system)).

user_help :-
  write_line(''),
  write_line('see  http://www.doc.ic.ac.uk/~or/proLogICA/tutorial.pdf'),
  write_line(''),
  write_line('use path / path(P) to see path or path(p) to set'),
  write_line('use file / file(F) to see file or file(f) to load'),
  write_line('use list to see clauses or advise(f) to write'),
  write_line('use set to see options or set(o,v) to set'),
  write_line('use demo([g],A) to run query, or eval([g],A) to minimise'),
  write_line(''),
  write_line('e.g. ?-path. or ?-path(\'c:/documents and settings/user\').'),
  write_line('e.g. ?-file. or ?-file(\'in.pl\').'),
  write_line('e.g. ?-list. or ?-advise(\'out.pl\').'),
  write_line('e.g. ?-set. or ?-set(max_ab_depth,50).'),
  write_line('e.g. ?-demo([goal],Ans). or ?-eval([goal],Ans).'),
  write_line(''),
  write_line('n.b. modeh(*,p(#t1,#t2)). makes atoms p(tt1,tt2) abducible ').

set :-  write('options are: '),
        val(Parameter,Value),
        format('~q=~q ',[Parameter,Value]),
        fail
        ;
        true.
        
set(Parameter,Value) :- 
        \+ ground(Parameter)-> write_line('specify parameter...'),fail ;
        \+ ground(Value)-> write_line('specify value...'),fail ;  
        retractall(val(Parameter,_)),     
        assert(val(Parameter,Value)),
        (initialised,mem(Parameter,[max_ic_unfold,exploit_determinism]))->write('RELOADING...'),reload;true . 
 
path :- path(Path),format('\n Path is ~q \n',[Path]).

path(Path) :- 
  ground(Path),!,
  working_directory(_,Path)
  ;
  working_directory(Path,Path).

reload :- file(X)->file(X);format('\n no file is loaded \n',[]).

file :- file(File)->format('\n File is ~q \n',[File]);format('\n no file is loaded \n',[]).

file(File) :- 
  ground(File),!,
  (absolute_file_name(File,_,[access(read),file_errors(fail)])
    ->  
        retract_dynamic,
        retractall(fname(_)),       
        retractall(initialised),
        load_files([File],[compilation_mode(consult)]),
        initialise,
        assert(fname(File))
     ;  
        write_line('file not found!')
  )

  ;
  
  fname(File).


make_dynamic(Pred/Arity) :- 
	current_predicate(Pred/Arity)
	->
	true
	;
	length(Vars,Arity),
	Atom =.. [Pred|Vars],
	assert(Atom),
	retract(Atom).

initialise :- 

  make_dynamic(initialised/0),
  make_dynamic(abducible_predicate/1),
  make_dynamic(modeh/2),
  make_dynamic(consistent/1),
  make_dynamic(closed_predicate/1),
  make_dynamic(ic/0),
  make_dynamic(ics/0),
  make_dynamic(icu/0),

  findall(_,(abducible_predicate(P),current_predicate(P,H),H=..[P|A],prefix('$tp_',P,T),N=..[T|A],assertz(N)),_),
  initialised->true;
  transform_head_decs,
  (
    option(max_ic_unfold,M),M=<0
    ->
    (bad_clause(C)->format('WARNING: clause "~q" \n defines an abducible, but renaming is currently disabled\n',[C]);true),
    (bad_ic(IC)->format('WARNING: constraint "~q" \n contains no abducible, but unfolding is currently disabled\n',[IC]);true),
    ((bad_clause(_);bad_ic(_))->format('SUGGEST: assigning "max_ic_unfold" a positive integer\n',[]);true)
    ;
    true
  ),
  initialise_closed_preds(X),
  initialise_auxiliary_preds(Y),
  initialise_ICs,
  X=X,Y=Y,
  write_all(['\n> closed predicates: ',X,'\n> auxiliary predicates: ',Y,'\n']),
  write('> ['),set,write(']\n'),
  asserta(initialised),
  nl.
    
pre_process(_InitGoals,_InitHyp,MaxAbDepth) :- 
  initialise,
  (option(showTime)->setTime;true),
  option(max_ab_depth,MaxAbDepth).

post_process(InHyp,InCon,Out) :- 
  option(max_ab_depth,MaxAbDepth),
  (option(max_ic_unfold,M),M>=0->
   % write_all(['\n\n    checking integrity of: ',InHyp,'\n']),
   % for SOCS % call((demo([not(ic),not(ics)],InHyp,InCon,InitHyp,InitCon,false,MaxAbDepth),!));
   call((demo([not(ic),not(ics)],InHyp,InCon,InitHyp,InitCon,false,MaxAbDepth)));
   InitHyp=InHyp,InitCon=InCon),  
  
  %write_all(['found: ',InitHyp,'\n']),
  
  remove_ab(InitHyp,FinalHyp),
  remove_ab(InitCon,FinalCon),
  
  (option(showTime)->getTime(Time);Time=0),
  name('Time=',TimeA),name(Time,TimeB),name('ms',TimeC),
  concat_all([TimeA,TimeB,TimeC],TimeD),name(TimeE,TimeD),
  (option(show_negatives)->OutA=FinalHyp;remove_not(FinalHyp,OutA)),
  (option(showTime)->concat(OutA,[<<<<<,TimeE],OutB);OutB=OutA),
  (option(show_constraints)->concat(OutB,[>>>>>,FinalCon],Out);Out=OutB).

%option(final_integrity_check):-!. 
%option(order_abducibles):-!.           
%option(show_bound_errors):-!.

%option(shared_var_frags):-!.

option(closed_pred_det):-!,val(enable_pruning,true). 
option(pure_frag_ex):-!,val(enable_pruning,true).    
option(closed_pred_det):-!,val(exploit_determinism,true).
option(require_minimal):-!,val(attempt_minimal,true).
option(attempt_minimal):-!,val(attempt_minimal,true).  
option(show_negatives):-!,val(show_negatives,true).  
option(debug_info):-!,val(debug_info,true).  
option(show_constraints):-!,val(show_constraints,true).   
option(showTime):-!,val(showTime,true). 
option(max_ab_depth,X):-!,val(max_ab_depth,X).    
option(max_con_depth,X):-!,val(max_con_depth,X).      
option(max_ic_unfold,X):-!,val(max_ic_unfold,X).   


% ================================================================ %
%                  DEDUCTION                          
% ================================================================ %

%assert_all([]).
%assert_all([H|T]):-assert(H),assert_all(T).
%
%retract_all([]).
%retract_all([H|T]):-retract(H),retract_all(T).
%
%deduce(Call):-
%	assert((not X :- \+ X)),
%	Call,	
%	abolish(not/1),
%	!.
%
%deduce(_):-
%	abolish(not/1),
%	fail.


% ============================================================ %
%                       USER OPTIONS                      
% ============================================================ %

:- dynamic val/2.

val(enable_pruning,true).    
val(exploit_determinism,true).    

val(attempt_minimal,false).  
val(show_negatives,false).  
val(debug_info,false).  
val(show_constraints,false).   
val(showTime,false).       

val(max_ab_depth,70).     % negative for depth-first
val(max_con_depth,50).      
val(max_ic_unfold,5).     % 0 for no unfold (ab or ic) 
                          % negative for no unfold or final ic check
                  



