import openai
import time
from keys import API_KEY,ORG_KEY

import argparse

openai.api_key= API_KEY
openai.organization = ORG_KEY


def get_response_4(prompt, prompt_cache, redo=False, temp=0.,max_tokens=30):

    if prompt in prompt_cache and not redo:
        return prompt_cache[prompt], prompt_cache

    else:
        passed = False; tries = 0 
        messages = [{'role': 'user', 'content': prompt}]
        while not passed:
            try:
                response = openai.ChatCompletion.create(
                    messages=messages,
                    model="gpt-4",
                    #model="gpt-3.5-turbo-0613",
                    temperature=0,
                    max_tokens=max_tokens)
                passed=True;tries+=1
                prompt_cache[prompt] = response
            except:
                time.sleep(.3)
                tries+=1
                if tries >=4:
                    pass#breakpoint()
                print(f'doing attempt number {tries +1}')

        return response, prompt_cache

def get_response_check_4(prompt, prompt_cache, temp=0,max_tokens=2000, redo=False):

    response, prompt_cache = get_response_4(prompt, prompt_cache, redo, temp=temp,max_tokens=max_tokens)
    #time.sleep(2)
    return response, prompt_cache

# BC domain -> ASP domain
bcdomain2asp = '''The programming language BC is an action language which has two kinds of constants, a fluent constant and an action constant. Answer Set Programming (ASP) is a logic programming paradigm. Given a domain specification in BC, generate ASP code which represents the supersorts (if applicable), sorts, choice rule for every fluent constant, choice rule for every action constant, inertial rules, and the uniqueness/existence constraint for each atom.
s_boolean(true;false) represents the boolean values true and false and is always used.
Write the constraints according to the given domains into BC:

Program 1:

Domain:
:- sorts
    loc >> block;
    block_w_none >> block;
    machine;
    gripper.

:- objects
    table :: loc;
    b1, b2, b3, b4 :: block;
    none :: block_w_none;
    m1, m2 :: machine;
    g1, g2, g3 :: gripper.

:- constants
    loc(block) :: inertialFluent(loc);
    gripped :: inertialFluent(block_w_none);
    in_tower(block) :: sdFluent;
    move(block, loc) :: action.

:-variables
    B, B1, B2 :: block;
    B_none :: block_w_none;
    L, L1 :: loc.


Generated constraints:

% supersorts
s_loc(B) :- s_block(B).
s_block_w_none :- s_block(B).

% sorts
s_boolean(true;false).
s_block_w_none(none).

s_loc(table).
s_block(b1;b2;b3;b4).
s_machine(m1;m2).
s_gripper(g1;g2).

% choice rule {0:A} for every atom A containing a regular fluent constant
{holds(loc(B,V),0)} :- s_block(B), s_loc(V).
{holds(gripped(V),0)} :- s_block_w_none(V).
{holds(in_tower(B,V),0)} :- s_block(B), s_boolean(V).


% choice rule {i:a} for every action constant a and every i < l
{occurs(move(B,L),T_step)} :- s_block(B), s_loc(L), timestep(T_step).

% Inertia

{holds(loc(B,V),T_step+1)} :-holds(loc(B,V),T_step), timestep(T_step).
{holds(gripped(V),T_step+1)} :-holds(gripped(V),T_step), timestep(T_step).
{holds(in_tower(B,V),T_step+1)} :-holds(in_tower(B,V),T_step), timestep(T_step).


% existence and uniqueness of value constraint

:- not {holds(loc(B,V),T_step): s_loc(V)}=1, s_block(B), timestep(T_step).
:- not {holds(gripped(V),T_step): s_block_w_none(V)}=1, timestep(T_step).
:- not {holds(in_tower(B,V),T_step): s_boolean(V)}=1, s_block(B), timestep(T_step).

Program 2:

Domain:
<DOMAIN>

Generated constraints:'''

# semi formal to shorthand BC
nl2bc = '''A program in BC consists of causal rules of the following 2 forms where their readings are shown after "%".
There are two kinds of constants, a fluent constant and an action constant. An  atom is of the form f=v, where f is a fluent constant, and v is an element of its domain. A fluent which has no argument, such as "hasGas" is assumed to be boolean. 

An expression of the form:
A_0 if A_1 & A_2 & ... & A_n

where A_i are atoms, expresses the static law that A_0 is true if the conjunction of A_1 & ... & A_n is true.

Example:
% The location of a person is the same as the car if the person is in the car.
loc(person)=L if inCar & loc(car)=L.
Note that the head of the rule (loc(person)=L in the example), must be only a single atom. So the following rule is not valid:
loc(person)=loc(car) if inCar.

An expression of the form:
F causes G if H

where  F is an action, G is an atom and H is a conjunction of atoms, expresses that action F causes G to be true if H is true. 

It also stands for the fluent dynamic law:
caused G after F & H
which expresses that atom G is causes after action F and atom H are true.

Example:
open(D) causes opened(D) if available(D).

Here are some common ways to write rules.

An expression of the form:
impossible A_1 & A_2 & ... & A_n

where A_i are atoms, is used to express that the conjunction of A_i is impossible.

Example:
impossible hasbrother(C) & ~hasSibling(C).
(note that impossible must only have conjunction (&), and cannot contain "if")
The form "impossible A_1 if ..." is incorrect while "impossible A_1 & ..." is correct.

For example, the following is incorrect:
impossible hasbrother(C) if ~hasSibling(C).

An expression of the form:
nonexecutable a_1 & ... & a_n if A_1 & A_2 & ... & A_m.

where a_i are actions and A_i are atoms, is used to express that an action cannot be executed if the conjunction of A_i is true.

Examples:
% It is not permissible to drive a car if it has no gas.
nonexecutable driveCar if ~hasGas.
% It is not permissible to lift an object if it is heavy.
nonexecutable lift(object) if heavy(object).

Example:
default onTable(B) if block(B). 

Examples
default door(open) if door(unlocked) after push(door).

In general, if something cannot be true, then we use "impossible" when writing the rules, but if instead we want to assert something is not true, then we use the negation (~). For example, if it is impossible for an object to be on the table and under it, we might write "impossible onTable(object) & underTable(object).", but express that if it rains outside the ground is not wet as "~groundWet if noRain".
Additionally, "impossible" is reserved only for fluents, while "nonexecutable" is only reserved for actions.

Here is an example representation.
Problem 1:
:- sorts
    thing;
    location.
:- objects
    monkey,bananas,box :: thing;
    l1,l2,l3 :: location.
:- variables
    Loc, Loc1, Loc2 :: location;
    Bool, Bool1, Bool2 :: boolean.
:- constants
    loc(thing) :: simpleFluent(location);
    hasBananas,onBox :: simpleFluent;
    walk(location) :: action;
    pushBox(location) :: action;
    climbOn :: action;
    climbOff :: action;
    graspBananas :: action.

Represent the following constraints:
% The location of the bananas is where the monkey is if the monkey has bananas.
% The location of the monkey is where the box is if the monkey is on the box.
% The monkey cannot be in two places at once.
% Walking to a location causes the monkey’s location to change.
% Walking is not permissible to a location if the monkey is already in that location
% Walking is not permissible if the monkey is on the box.
% Pushing the box to a location causes the location of the box to move.
% Pushing the box to a location causes the location of the monkey to move.
% Pushing the box is not permissible to a location if the monkey is at that location
% Pushing the box is not permissible if the monkey is on the box.
% Pushing the box is not permissible if the location of the monkey is not the same as the location of the box.
% Climbing on the box causes the monkey to be on the box.
% Climbing on the box is not permissible if the monkey is already on the box.
% Climbing on the box is not permissible if the location of the monkey is not the same as the box.
% Climbing off of the box causes the monkey to not be on the box.
% Climbing off of the box is not permissible if the monkey is not on the box.
% Grasping the bananas causes the monkey to have the bananas.
% Grasping the bananas is not permissible if the monkey already has the bananas.
% Grasping the bananas is not permissible if the monkey is not on the box.
% Grasping the bananas is not permissible if the location of the monkey is not the same as the location of the bananas.
% It is not permissible to both walk to a location and push the box to a location.
% It is not permissible to both walk to a location and climb on the box.
% It is not permissible to both push the box to a location and climb on the box.
% It is not permissible to both climb off of the box and grasp the bananas.

Constraints (only use fluents and actions specified for the problem):
% The location of the bananas is where the monkey is if the monkey has bananas.
loc(bananas)=L if hasBananas & loc(monkey)=L.

% The location of the monkey is where the box is if the monkey is on the box.
loc(monkey)=L if onBox & loc(box)=L.

% The monkey cannot be in two places at once.
impossible loc(monkey) = L1 & loc(monkey)=L2 & L1\=L2.

% Walking to a location causes the monkey’s location to change.
walk(L) causes loc(monkey)=L.

% Walking is not permissible to a location if the monkey is already in that location
nonexecutable walk(L) if loc(monkey)=L.

% Walking is not permissible if the monkey is on the box.
nonexecutable walk(L) if onBox.

% Pushing the box to a location causes the location of the box to move.
pushBox(L) causes loc(box)=L.

% Pushing the box to a location causes the location of the monkey to move.
pushBox(L) causes loc(monkey)=L.

% Pushing the box is not permissible to a location if the monkey is at that location
nonexecutable pushBox(L) if loc(monkey)=L.

% Pushing the box is not permissible if the monkey is on the box.
nonexecutable pushBox(L) if onBox.

% Pushing the box is not permissible if the location of the monkey is not the same as the location of the box.
nonexecutable pushBox(L) if loc(monkey)\=loc(box).

% Climbing on the box causes the monkey to be on the box.
climbOn causes onBox.

% Climbing on the box is not permissible if the monkey is already on the box.
nonexecutable climbOn if onBox.

% Climbing on the box is not permissible if the location of the monkey is not the same as the box.
nonexecutable climbOn if loc(monkey)\=loc(box).

% Climbing off of the box causes the monkey to not be on the box.
climbOff causes ~onBox.

% Climbing off of the box is not permissible if the monkey is not on the box.
nonexecutable climbOff if ~onBox.

% Grasping the bananas causes the monkey to have the bananas.
graspBananas causes hasBananas.

% Grasping the bananas is not permissible if the monkey already has the bananas.
nonexecutable graspBananas if hasBananas.

% Grasping the bananas is not permissible if the monkey is not on the box.
nonexecutable graspBananas if ~onBox.

% Grasping the bananas is not permissible if the location of the monkey is not the same as the location of the bananas.
nonexecutable graspBananas if loc(monkey)\=loc(bananas).

% It is not permissible to both walk to a location and push the box to a location.
nonexecutable walk(L) & pushBox(L).

% It is not permissible to both walk to a location and climb on the box.
nonexecutable walk(L) & climbOn.

% It is not permissible to both push the box to a location and climb on the box.
nonexecutable pushBox(L) & climbOn.

% It is not permissible to both climb off of the box and grasp the bananas.
nonexecutable climbOff & graspBananas.

Problem 2:
Given the following domain:
<DOMAIN>

Write the following constraints:
<CONSTRAINTS>

Constraints (only use fluents and actions specified for the problem):'''

# shorthand BC to expanded BC
sh2bc = '''The programming language BC is an action language which has two kinds of constants, a fluent constant and an action constant. An atom is of the form f=v, where f is a fluent constant, and v is an element of its domain. There are some shorthand rules which are described below. The shorthand versions expand into another form via a translation.


Rules in this form are not changed.
Example: 
Original rule: loc(person)=L if inCar & loc(car)=L.
Translation: loc(person)=L if inCar & loc(car)=L.


Example:
Original rule: status(light) = on after switch(on).
Translation: status(light) = on after switch(on).

ACTIONS

Example:
Original rule: drive(C,L) causes loc(C) = L.
Translation: loc(C)=L after drive(C,L).

Example:
Original rule: loc(car) = home & drive(home) & loc(car) = bank.
Translation: loc(car)  = home after drive(home) & loc(car) = bank.

DEFAULTS

Example:
Original Rule: default onTable(B) if color(B)=red.
Translation: onTable(B) if color(B) if cons onTable(B).

Example:
Original rule: default ~onTable(B) if pickedUp(B).
Translation: ~onTable(B) after pickedUp(B) if cons ~onTable(B).

IMPOSSIBLE

Example:
Original rule: impossible hasbrother(C) & ~hasSibling(C).
Translation: false if hasbrother(C) & ~hasSibling(C).

NONEXECUTABLE

Example:
Original rule: nonexecutable lift(object) if weight(object)=heavy.
Translation: false after lift(object) & weight(object)=heavy.

Translate the following programs:

Program 1

Domain:
:- sorts
    loc >> block;
    block_w_none >> block;
    machine;
    gripper.

:- objects
    table :: loc;
    b1, b2, b3, b4 :: block;
    m1, m2 :: machine;
    g1, g2, g3 :: gripper.

:- constants
    loc(block) :: inertialFluent(loc);
    gripped :: inertialFluent(block+none);
    in_tower(block) :: sdFluent;
    move(block, loc) :: action.

:-variables
    B, B1, B2 :: block;
    L, L1 :: loc.

Original rules:
% 1. Two blocks cannot be at the same location.
impossible loc(B1) = B & loc(B2) = B & B1\=B2.

% 2.1 A block is in a tower if it's location is on the table.
in_tower(B) if loc(B) = table.

% 2.2 A block is in a tower if it's location is on something that is in a tower.
in_tower(B) if loc(B) = B1 & in_tower(B1).

% 3. Blocks don't float in the air.
impossible ~in_tower(B).

% 4. Moving a block causes it's location to move to loc.
move(B,L) causes loc(B)=L.

% 5. The move action is impermissible if something is on the location to be moved to.
nonexecutable move(B,L) if loc(B1) = B.

% 6. By default, a block is not in the tower.
default ~in_tower(B).

% 7. The move action causes nothing to be gripped.
move(B,L) causes gripped(none).

Translation:


% 1. Two blocks cannot be at the same location.
false if loc(B1) = B & loc(B2) = B and B1\=B2.

% 2.1 A block is in a tower if it's location is on the table.
in_tower(B) if loc(B) = table.

% 2.2 A block is in a tower if it's location is on something that is in a tower.
in_tower(B) if loc(B) = B1 & in_tower(B1).

% 3. Blocks don't float in the air.
false if ~in_tower(B).

% 4. Moving a block causes it's location to move to loc.
loc(B)=L after move(B,L).

% 5. The move action is impermissible if something is on the location to be moved to.
false after move(B,L) & loc(B1) = B.

% 6. By default, a block is not in the tower.
~in_tower(B) if cons ~in_tower(B).

% 7. The move action causes nothing to be gripped.
gripped(none) if move(B,L).

Program 2

Domain:
<DOMAIN>

Original rules:
<RULES>

Translation:'''

# expanded BC to ASP
bc2asp = '''The programming language BC is an action language which has two kinds of constants, a fluent constant and an action constant. An atom is of the form f=v, where f is a fluent constant, and v is an element of its domain. These rules eventuall get translated into another form.

Atoms are generally in the form "f=v", but can be written short form "f" if it represents a boolean variable, and hence "v" is true and false.

Here, we will translate rules and their atoms. If the atom is of the form "f=v", then it will be copied as "holds(f(v),i)" according to the translation, where v is an element in f's domain. If it is of the form of "f", then it will be copied as "holds(f(v),I)", where v is either true or false. I is a timestamp.

For example, the atom "loc(car)=L" may be translated to "holds(loc(car, L),I)", and the atom "door(open)" may be translated into "holds(door(open, true),I)" or "holds(door(open,false),I)" since it is boolean. 

Static laws:

Example:
Original rule: loc(person)=L if inCar & loc(car)=L if cons on(car).
Translation: holds(loc(person,L),I) :- holds(incar(true),I), holds(loc(car,L),I), not not holds(on(car, true),I), timestep(I).

Example:
Original rule: false if hasbrother(C) & ~hasSibling(C).
Translation::- holds(hasbrother(C,true),I), holds(hasSibling(C,false),I), timestep(I).

Dynamic laws:

Example:
Original rule: status(light) = on after switch(on) if cons power(on) & connected.
Translation: holds(status(light,on),I+1) :- holds(switch(on,true),I), not not holds(power(on,true),I+1), not not holds(connected(true),I+1), timestep(I).

Example:
Original rule: false after lift(O) & weight(O)=heavy.
Translation: :- occurs(lift(object),I), holds(weight(O,heavy),I), timestep(I).

Translate the following programs:

Program 1:

BC Domain:
:- sorts
    loc >> block;
    block_w_none >> block;
    machine;
    gripper.

:- objects
    table :: loc;
    b1, b2, b3, b4 :: block;
    m1, m2 :: machine;
    g1, g2, g3 :: gripper.

:- constants
    loc(block) :: inertialFluent(loc);
    gripped :: inertialFluent(block+none);
    in_tower(block) :: sdFluent;
    move(block, loc) :: action.

ASP Domain:

% supersorts
s_loc(B) :- s_block(B).

% sorts
s_boolean(true;false).  

s_loc(table).
s_block(b1;b2;b3;b4).  
s_machine(m1;m2).
s_gripper(g1;g2).

% choice rule {0:A} for every atom A containing a regular fluent constant
{holds(loc(B,V),0)} :- s_block(B), s_loc(V).
{holds(gripper(V),0)} :- s_block_w_none(V).
{holds(in_tower(B,V),0)} :- s_block(B), s_boolean(V).

% choice rule {i:a} for every action constant a and every i < l
{occurs(move(B,L),T_step)} :- s_block(B), s_loc(L), timestep(T_step).

% Inertia

{holds(loc(B,V),T_step+1)} :-holds(loc(B,V),T_step), timestep(T_step).
{holds(gripped(V),T_step+1)} :-holds(gripped(V),T_step), timestep(T_step).
{holds(in_tower(B,V),T_step+1)} :-holds(in_tower(B,V),T_step), timestep(T_step).

% existence and uniqueness of value constraint

:- not {holds(loc(B,V),T_step): s_loc(V)}=1, s_block(B), timestep(T_step).
:- not {holds(gripped(V),T_step): s_block_w_none(V)}=1, timestep(T_step).
:- not {holds(in_tower(B,V),T_step): s_boolean(V)}=1, s_block(B), timestep(T_step).


Rules:
% 1. Two blocks cannot be at the same location.
false if loc(B1) = B & loc(B2) = B and B1\=B2.

% 2.1 A block is in a tower if it's location is on the table.
in_tower(B) if loc(B) = table.

% 2.2 A block is in a tower if it's location is on something that is in a tower.
in_tower(B) if loc(B) = B1 & in_tower(B1).

% 3. Blocks don't float in the air.
false if ~in_tower(B).

% 4. Moving a block causes it's location to move to loc.
loc(B)=L after move(B,L).

% 5. The move action is impermissible if something is on the location to be moved to.
false after move(B,L) & loc(B1) = B.

% 6. By default, a block is not in the tower.
~in_tower(B) if cons ~in_tower(B).

% 7. The move action causes nothing to be gripped.
gripped=none if move(B,L).

Translation:
% 1. Two blocks cannot be at the same location.
:- holds(loc(B1,B),T_step), holds(loc(B2,B),T_step), B1!=B2, s_block(B), s_block(B1), s_block(B2), timestep(T_step).

% 2.1 A block is in a tower if it's location is on the table.
holds(in_tower(B,true),T_step) :- holds(loc(B,table),T_step), s_block(B), timestep(T_step).

% 2.2 A block is in a tower if it's location is on something that is in a tower.
holds(in_tower(B,true),T_step) :- holds(loc(B,B1),T_step), holds(in_tower(B1,true),T_step), s_block(B), s_block(B1), timestep(T_step).

% 3. Blocks don't float in the air.
:- holds(in_tower(B,true),T_step), s_block(B), timestep(T_step).

% 4. Moving a block causes it's location to move to loc.
holds(loc(B,L),T_step+1) :- occurs(move(B,L),T_step), s_block(B), s_loc(L), timestep(T_step).

% 5. The move action is impermissible if something is on the location to be moved to.
:- occurs(move(B,L),T_step), holds(loc(B1,B),T_step), s_block(B), s_block(B1), s_loc(L), timestep(T_step).

% 6. By default, a block is not in the tower.
holds(in_tower(B,false),T_step) :- not not holds(in_tower(B,false),T_step), s_block(B), timestep(T_step).

% 7. The move action causes nothing to be gripped.
holds(gripped(none),T_step+1) :- occurs(move(B,L),T_step), s_block(B), s_loc(L).

Program 2:

BC Domain:
<DOMAIN>

ASP Domain:
<ASPDOMAIN>

Rules:
<RULES>

Translation:'''

# natural language to semiformal statements
nl2sf = '''Given a description of a problem, write commonsense knowledge about the domain that we would expect. These represent logical constraints in the problem.

For example, a task about moving objects would involve some knowledge about what is required to move, what the effect of moving an object does, such as the location of the object changing or its previous location now being empty. 

These restrictions and effects are dependent on the context of the problem. Here we list some example problems and extract commonsense knowledge.

Problem 1
Description:
A monkey wants to get a bunch of bananas hanging from the ceiling. He can reach the bananas by first pushing a box to the empty place under the bananas and then climbing on top of the box. The task is to come up with a plan for retrieving the bananas.
Some things to consider are the monkey, the bananas, the box, the location of objects, and the monkey's ability to move and push the box. Provide the relevant commonsense knowledge. Only use the terminology in the hint to write the commonsense knowledge.

Hint:
There are two main types of things: "things" and "location".

monkey, bananas, and box are things.
l1, l2, and l3 are locations.

Fluents:
A (thing)'s location is a simple fluent (location).
Having bananas is a simple fluent (boolean).
Being on the box are simple fluents (boolean).

Actions:
walk to a (location)
push box to a (location)
climb on
climb off
grasp bananas

Commonsense knowledge (do not provide any extra knowledge that is not included in the description):
% The location of the bananas is where the monkey is if the monkey has bananas.
% The location of the monkey is where the box is if the monkey is on the box.
% Walking to a location causes the monkey’s location to change.
% Walking is not permissible to a location if the monkey is already in that location
% Walking is not permissible if the monkey is on the box.
% Pushing the box to a location causes the location of the box to move.
% Pushing the box to a location causes the location f the monkey to move.
% Pushing the box is not permissible to a location if the monkey is at that location
% Pushing the box is not permissible if the monkey is on the box.
% Pushing the box is not permissible if the location of the monkey is not the same as the location of the box.
% Climbing on the box causes the monkey to be on the box.
% Climbing on the box is not permissible if the monkey is already on the box.
% Climbing on the box is not permissible if the location of the monkey is not the same as the box.
% Climbing off of the box causes the monkey to not be on the box.
% Climbing off of the box is not permissible if the monkey is not on the box.
% Grasping the bananas causes the monkey to have the bananas.
% Grasping the bananas is not permissible if the monkey already has the bananas.
% Grasping the bananas is not permissible if the monkey is not on the box.
% Grasping the bananas is not permissible if the location of the monkey is not the same as the location of the bananas.
% It is not permissible to both walk to a location and push the box to a location.
% It is not permissible to both walk to a location and climb on the box.
% It is not permissible to both push the box to a location and climb on the box.
% It is not permissible to both climb off of the box and grasp the bananas.

Problem 2:
Description:
<PROBLEM DESCRIPTION>

Hint:
<HINT>
Commonsense knowledge (do not provide any extra knowledge that is not included in the description):'''

# semi formal to BC domain
sf2bcdomain = '''Action language BC specifies the syntax of the domain in the form of sorts, objects, variables, and constants. 

A sort is a named set of elements which is used to specify the domain of each constant and variable. First the sort is declared
using a sort declaration statement and, later, is defined by adding objects to it in an object declaration statement.

Sort declaration:
:- sorts
    int;
    box.

This declares the domains: int, and box.

An object is a value in a sort which a constant can take. It is also used
in parameter lists to construct nested objects and sets of constants. 

Object declaration:
:- objects
    1..3 :: int;
    o(int, int) :: box.

This declares 1,2, and 3 as objects within int, and the objects:
o(1, 1), o(1, 2), o(1, 3),
o(2, 1), o(2, 2), o(2, 3),
o(3, 1), o(3, 2), and o(3, 3),
as values within box.

A variable is a placeholder symbol which will be replaced with each object in its domain during grounding.

Variable declaration:
:- variables
    I, I1, I2 :: int;
    B, B1, B2 :: box.
This declares the variables I, I1, and I2 over the objects within int, and variables B, B1, and B2 range over the objects within box.

Constant symbols are the basic components of multivalued formulas. Similar to object symbols, constants are defined within a constant declaration statement and have a base identifier, an optional list of parameter sort, and a sort which makes up the constant’s domain. In addition, they may have a constant declaration type, such as "action", "simpleFluent", and "inertialFluent". Inertial fluents are used for constants whose value persists through time unless affected otherwise.
Constant declaration:
:- constants
    p(int) :: inertialFluent;
    move(box) :: action.
This declares the inertial fluent p which takes an int argument, and the action move, which takes a box argument.

Given some knowledge about a domain, produce the sorts, objects, variables, and constants for the action language BC. 

Problem 1
Problem description:
A monkey wants to get a bunch of bananas hanging from the ceiling. He can reach the bananas by first pushing a box to the empty place under the bananas and then climbing on top of the box.

Hint:
There are three main types of things: "monkey", "thing" and "location".
"thing" includes "monkey".

monkey, bananas, and box are things.
l1, l2, and l3 are locations.

Fluents:
A (thing)'s location is a simple fluent (location).
Having bananas is a simple fluent (boolean).
Being on the box are simple fluents (boolean).

Actions:
walk to a (location)
push box to a (location)
climb on
climb off
grasp bananas

Knowledge:
% The location of the bananas is where the monkey is if the monkey has bananas.
% The location of the monkey is where the box is if the monkey is on the box.
% Walking to a location causes the monkey’s location to change.
% Walking is not permissible to a location if the monkey is already in that location
% Walking is not permissible if the monkey is on the box.
% Pushing the box to a location causes the location of the box to move.
% Pushing the box to a location causes the location f the monkey to move.
% Pushing the box is not permissible to a location if the monkey is at that location
% Pushing the box is not permissible if the monkey is on the box.
% Pushing the box is not permissible if the location of the monkey is not the same as the location of the box.
% Climbing on the box causes the monkey to be on the box.
% Climbing on the box is not permissible if the monkey is already on the box.
% Climbing on the box is not permissible if the location of the monkey is not the same as the box.
% Climbing off of the box causes the monkey to not be on the box.
% Climbing off of the box is not permissible if the monkey is not on the box.
% Grasping the bananas causes the monkey to have the bananas.
% Grasping the bananas is not permissible if the monkey already has the bananas.
% Grasping the bananas is not permissible if the monkey is not on the box.
% Grasping the bananas is not permissible if the location of the monkey is not the same as the location of the bananas.
% It is not permissible to both walk to a location and push the box to a location.
% It is not permissible to both walk to a location and climb on the box.
% It is not permissible to both push the box to a location and climb on the box.
% It is not permissible to both climb off of the box and grasp the bananas.

BC domain syntax:
:- sorts
    thing >> monkey;
    location.
:- objects
    monkey,bananas,box :: thing;
    l1,l2,l3 :: location.
:- variables
    Loc, Loc1, Loc2 :: location;
    Bool, Bool1, Bool2 :: boolean.
:- constants
    loc(thing) :: simpleFluent(location);
    hasBananas,onBox :: simpleFluent;
    walk(location) :: action;
    pushBox(location) :: action;
    climbOn :: action;
    climbOff :: action;
    graspBananas :: action.


Problem 2
Problem description:
<PROBLEM DESCRIPTION>

Hint:
<HINT>

Knowledge:
<KNOWLEDGE>

BC domain syntax:'''

# query hint to ASP query
nl2query = '''Given the domain in ASP, convert the natural language queries into ASP form.

Program 1:

ASP Domain:
% supersorts
s_loc(B) :- s_block(B).

% sorts
s_boolean(true;false).  

s_loc(table).
s_block(b1;b2;b3;b4).  
s_machine(m1;m2).
s_gripper(g1;g2).

% choice rule {0:A} for every atom A containing a regular fluent constant
{holds(loc(B,V),0)} :- s_block(B), s_loc(V).
{holds(gripper(V),0)} :- s_block_w_none(V).
{holds(in_tower(B,V),0)} :- s_block(B), s_boolean(V).

% choice rule {i:a} for every action constant a and every i < l
{occurs(move(B,L),T_step)} :- s_block(B), s_loc(L), timestep(T_step).

% Inertia

{holds(loc(B,V),T_step+1)} :-holds(loc(B,V),T_step), timestep(T_step).
{holds(gripped(V),T_step+1)} :-holds(gripped(V),T_step), timestep(T_step).
{holds(in_tower(B,V),T_step+1)} :-holds(in_tower(B,V),T_step), timestep(T_step).

% existence and uniqueness of value constraint

:- not {holds(loc(B,V),T_step): s_loc(V)}=1, s_block(B), timestep(T_step).
:- not {holds(gripped(V),T_step): s_block_w_none(V)}=1, timestep(T_step).
:- not {holds(in_tower(B,V),T_step): s_boolean(V)}=1, s_block(B), timestep(T_step).

Queries:
% Block b1 is on block b2 at time 0.

% Block b3 is moved onto block b4 at time 3.

% At time step 6, block b4 is on b3, b3 is on b2, and b2 is on b1.

ASP form:
% initially, block b1 is on block b2 at time 0.
holds(loc(b1,b2),0).

% block b3 is moved onto block b4 at time 3.
:- not occurs(move(b3),b4),3).

% At time step 6, block b4 is on b3, b3 is on b2, and b2 is on b1.
:- not holds(loc(b4,b3),0).
:- not holds(loc(b3,b2),0).
:- not holds(loc(b2,b1),0).

Program 2:
ASP Domain:
<ASP DOMAIN>

Queries:
<QUERIES>

ASP form:'''

import pickle
import os
parser = argparse.ArgumentParser()
parser.add_argument('--o', default='output_file', type=str,
    help='the output file name')
args = parser.parse_args()
args.o = args.o+'.csv' if '.csv' not in args.o else args.o

if 'prompt_cache_gpt-4.pickle' in os.listdir():
    with open('prompt_cache_gpt-4.pickle', 'rb') as handle:
        prompt_cache = pickle.load(handle)
else:
    prompt_cache = dict()

from domains import problem_dict

response_dict = {}
user_inputs = []
problem_prompts = []
responses={}
problem_dict = {key:item for key,item in problem_dict.items() if key in ['shooting', 'hanoi', 'switches', 'lifting']}

for prob_name,prob in problem_dict.items():
    domain,_, prob_desc, query, hint = prob
    prompt_prompt=[]
    user_inputs.append([prob_desc, domain, query])
    input_string = ('\n'+'-'*70+'\n\n\n\n').join([prob_desc, query])
    
    prompt_prompt.append(input_string)

    responses[prob_name]=['']
    desc2sf_prompt = nl2sf.replace('<PROBLEM DESCRIPTION>',prob_desc).replace('<HINT>',hint)
    prompt_prompt.append(desc2sf_prompt)
    response, prompt_cache = get_response_check_4(desc2sf_prompt, prompt_cache)
    response_text_desc2sf = response['choices'][0]['message']['content']
    responses[prob_name].append(response_text_desc2sf)

    knowledge = response_text_desc2sf
   
    domain_prompt = sf2bcdomain.replace('<PROBLEM DESCRIPTION>',prob_desc).replace('<HINT>',hint).replace('<KNOWLEDGE>', knowledge)
    prompt_prompt.append(domain_prompt)
    response, prompt_cache = get_response_check_4(domain_prompt, prompt_cache)
    response_text_BC_domain = response['choices'][0]['message']['content']
    responses[prob_name].append(response_text_BC_domain)

    # use generated BC domain as domain
    domain = response_text_BC_domain

    domain_prompt = bcdomain2asp.replace('<DOMAIN>',domain)
    prompt_prompt.append(domain_prompt)
    response, prompt_cache = get_response_check_4(domain_prompt, prompt_cache)
    response_text_asp_domain = response['choices'][0]['message']['content']
    responses[prob_name].append(response_text_asp_domain)

    
    constraints = response_text_desc2sf
    problem_prompt = nl2bc.replace('<DOMAIN>',domain).replace('<CONSTRAINTS>',constraints)
    prompt_prompt.append(problem_prompt)
    response, prompt_cache = get_response_check_4(problem_prompt, prompt_cache)
    response_text = response['choices'][0]['message']['content']
    responses[prob_name].append(response_text)
    

    prompt = sh2bc.replace('<DOMAIN>',domain).replace('<RULES>',response_text)
    prompt_prompt.append(prompt)
    response, prompt_cache = get_response_check_4(prompt, prompt_cache)
    response_text = response['choices'][0]['message']['content']
    responses[prob_name].append(response_text)
    
    
    prompt = bc2asp.replace('<DOMAIN>',domain).replace('<ASPDOMAIN>',response_text_asp_domain).replace('<RULES>',response_text)
    prompt_prompt.append(prompt)
    response, prompt_cache = get_response_check_4(prompt, prompt_cache)
    response_text = response['choices'][0]['message']['content']
    responses[prob_name].append(response_text)
    
    prompt = nl2query.replace('<ASP DOMAIN>',response_text_asp_domain).replace('<QUERIES>',query)
    prompt_prompt.append(prompt)
    response, prompt_cache = get_response_check_4(prompt, prompt_cache)
    response_text = response['choices'][0]['message']['content']
    responses[prob_name].append(response_text)
    

    problem_prompts.append(prompt_prompt)
    
    with open('prompt_cache_gpt-4.pickle', 'wb') as handle:
        pickle.dump(prompt_cache, handle, protocol=pickle.HIGHEST_PROTOCOL)
#breakpoint()

import csv

csv_form = []
csv_form.append(['Domain name', 'User Inputs', 'description -> semi-formal', 'semi-formal -> BC domain', 'Domain prompt (bcdomain2asp)', 'NL -> shorthand BC (nl2bc)', 'shorthand BC -> BC (sh2bc)', 'BC -> ASP (bc2asp)', 'NL query -> ASP query', 'All responses/All responses without intermediate BC', 'BC Program', 'ASP Program'])
for idx,key in enumerate(problem_dict):
    semi_formal = responses[key][4]
    bc_domain = responses[key][2]
    
    asp_domain = responses[key][3]
    asp_rules = responses[key][6]
    asp_query = responses[key][7]
    
    bc_program = bc_domain + '\n'*3 + semi_formal
    asp_program = ('\n'*3).join([asp_domain, asp_rules, asp_query])
    csv_form.append([key + ' prompts'] + [pp + '\n\n' + rr for (pp,rr) in zip(problem_prompts[idx],responses[key])] + ['\n\n\n'.join(responses[key])] + [bc_program, asp_program])
    #csv_form.append([key + ' responses'] + responses[key]+ ['\n\n\n'.join([resp for idx,resp in enumerate(responses[key]) if idx in [1,5,6]])])
#csv_form = [l for l in responses.values()]


with open(args.o, "w", newline='') as f:
    writer = csv.writer(f)
    writer.writerows(csv_form)


