bw = ''':- sorts
        loc >> block.

:- objects
        b1, b2, b3, b4 :: block;
        table :: loc.

:- constants
        loc(block)              :: inertialFluent(loc);
        in_tower(block) :: sdFluent;
        move(block, loc):: action.

:- variables
        B, B1, B2       :: block;
        L, L1           :: loc.

% location
impossible loc(B1) = B & loc(B2) = B where B1\=B2.

% Definition of a tower
%default ~in_tower(B).
in_tower(B) if loc(B) = table.
%in_tower(B) if loc(B) = B1 & in_tower(B1).

% Blocks don't float in the air
%impossible ~in_tower(B).

% Moving a block
%move(B,L) causes loc(B)=L.

%nonexecutable move(B,L) if loc(B1) = B.

%:- query
%       label :: stack;
%       0: loc(B)=table;
%       maxstep: loc(b4)=b3 & loc(b3)=b2 & loc(b2)=b1.
'''


bw_alt = ''':- macros
        N -> 4; M -> 5.

:- sorts
        loc >> block;
        loc >> table;
        gripper.

:- objects
        blk(1..N)                               :: block;
        tbl(1..M)                               :: table;
        left, right                             :: gripper.

:- constants
        on(block)                               :: inertialFluent(loc);
        pos(loc)                                :: sdFluent(table*);
        move(gripper,block,loc) :: action.

:- variables
        I                                               :: 1..N;
        B, B1, B2                               :: block;
        T                                               :: table;
        L, L1, L2                               :: loc;
        G                                               :: gripper.

false if on(B1)=L & on(B2)=L where B1\=B2.

default pos(B)=none.
pos(T)=T.
pos(B)=T if on(B)=L & pos(L)=T.
false if pos(B)=none.

move(G,B,L) causes on(B)=L.
false after move(G,B,L) & move(G,B1,L1)
        where B\=B1.


:- query
        label :: stack;
        0: on(blk(I))=tbl(I);
        maxstep: pos(B)=tbl(1).
'''



'''Please represent a problem description with a program in action language BC.

A program in BC consists of causal rules of the following 2 forms where their readings are shown above after "%".



% action G cannot be executeed if H is true
nonexecutable G if H.

% G must be false
impossible G.

% By default, A is true if G is true after H happens, as long as A is consistent with G
default A if G after H.

% the action a causes F to hold if H is true
a causes F if H

Here is an example representation.
'''

prompt = '''A program in BC consists of causal rules of the following 2 forms where their readings are shown after "%".
There are two kinds of constants, a fluent constant and an action constant. An  atom is of the form f=v, where f is a fluent constant, and v is an element of its domain. A fluent which has no argument, such as "hasGas" is assumed to be boolean. An action atom is 
A static law of is generally written as the form:
F if G1 ifcons G2,
where F is an atom, and G1 and G2 are conjunctions of atoms. Intuitively, it reads If G1 is satisfied in the current state and it is consistent to assume that G2 is satisfied, then F must also be satisfied in the current state.
(only a single fluent atom can be in the head of the rule, i.e., "F if G1 if cons G2" is allowed, but "F1=F2 if G1 if cons G2" is not allowed)
For example:
location(car) = garage if parked(car) ifcons location(henry)=home.

A dynamic law is generally written as the form:
F if G1 if cons G2 after H,
where F is an atom, G1 and G2 are conjunctions of atoms, and H is a conjunction of atoms and actions. Intuitively it reads, if the fluent atoms in H were satisfied in the last state and the actions in H occurred, G1 is true in the current state, and it is consistent to assume that G2 is true in the current state, then F must also be true in the current state.
For example:
location(henry) = store ifcons inCar(Henry) after drive(store).

Here are some common ways to write rules.
% Static law: Fluent F is true if fluent G is true.
F if G.
Example:
% The location of a person is the same as the car if the person is in the car.
loc(person)=L if inCar & loc(car)=L.
Note that the head of the rule (loc(person)=L in the example), must be only a single atom. So the following rule is not valid:
loc(person)=loc(car) if inCar.

% Static law: G must be false, where G is an atom (or conjunction of atoms):
f=v after G.
f=w after G.
This is will make the program false, and is written shorthand as:
impossible G.
Example:
impossible hasbrother(C) & ~hasSibling(C).
(note that impossible can only have conjunction (&), and cannot contain "if".

% Static law: By default, atom A is true if atom G (or conjunction of atoms) is true:
default A if G.
Example:
default onTable(B).

% Dynamic law: By default, atom A is true if atom G is true after atom H happens:
default A if G after H.
Example:
default door(open) if door(unlocked) after push(door).

% Dynamic law: Action a causes f to be true.
a after F.
A general and intuitive way to write this is, the action a causes atom F to hold if atom H is true:
a causes F if H.
example:
open(D) causes opened(D) if available(D).

% Dynamic law: action a cannot be executeed if atom H is true:
f=v after a, if H.
f=w after a, if H.
This will make the program false, and is written shorthand with the keyword "nonexecutable":
nonexecutable a if H.
Examples:
% It is not permissible to drive a car if it has no gas.
nonexecutable driveCar if ~hasGas.
% It is not permissible to lift an object if it is heavy.
nonexecutable lift(object) if heavy(object).

In general, if something cannot be done, then we use "impossible" when writing the rules, but if instead something just, is not, then we use the negation ~. For example, if it is impossible for an object to be on the table and under it, we might write "impossible onTable(object) & underTable(object).", but express that if it rains outside the ground is not wet as "~groundWet if noRain".
Additionally, "impossible" is reserved only for fluents, while "nonexecutable" is only reserved for actions.

Here is an example representation.
Problem 1:
Given the following domain:
blocks: b1, b2, b3, b4.
locations: blocks + {table}
variables:
block: B, B1, B2.
loc: L, L1.
constants:
- loc(block) :: inertialFluent.
- in_tower(block) :: sdFluent.
- move(block, loc) :: action.

Represent the following constraints:
% 1. Two blocks cannot be at the same location.
% 2.1 A block is in a tower if it's location is on the table.
% 2.2 A block is in a tower if it's location is on something that is in a tower.
% 3. Blocks don't float in the air.
% 4. Moving a block causes it's location to move to loc.
% 5. The move action is not executable if something is on the location to be moved to.

Constraints:
% 1. Two blocks cannot be at the same location.
impossible loc(B1) = B & loc(B2) = B where B1\=B2.

% 2.1 A block is in a tower if it's location is on the table.
in_tower(B) if loc(B) = table.

% 2.2 A block is in a tower if it's location is on something that is in a tower.
in_tower(B) if loc(B) = B1 & in_tower(B1).

% 3. Blocks don't float in the air.
impossible ~in_tower(B).

% 4. Moving a block causes it's location to move to loc.
move(B,L) causes loc(B)=L.

% 5. The move action is permissible if something is on the location to be moved to.
nonexecutable move(B,L) if loc(B1) = B.

Problem 2:
Given the following domain:
<DOMAIN>

Write the following constraints:
<CONSTRAINTS>

Constraints:
'''

prompt = '''A program in BC consists of causal rules of the following 2 forms where their readings are shown after "%".
There are two kinds of constants, a fluent constant and an action constant. An atom is of the form f=v, where f is a fluent constant, and v is an element of its domain. A fluent which has no argument, such as "hasGas" is assumed to be boolean. An action atom is 

Here are some common ways to write rules.
% Static law: Atom F is true if atom G is true.
F if G.
Example:
% The location of a person is the same as the car if the person is in the car.
loc(person)=L if inCar & loc(car)=L.
Note that the head of the rule (loc(person)=L in the example), must be only a single atom. So the following rule is not valid:
loc(person)=loc(car) if inCar.

% Static constraint: A pair of static laws, where G is an atom (or conjunction of atoms), and v and w are distinct:
f=v if G.
f=w if G.
Both f=v and f=w will make the program false. This constraint is written shorthand as:
impossible G.
Example:
impossible hasbrother(C) & ~hasSibling(C).
(note that impossible can only have conjunction (&), and cannot contain "if".

% Static law: By default, atom A is true if atom G (or conjunction of atoms) is true:
default A if G. % "if G" is optional
Example:
default onTable(B) if block(B). 

% Dynamic law: Action a causes f to be true.
F after a.
A general and intuitive way to write this is, the action a causes atom F to hold if atom H is true:
a causes F if H.
example:
open(D) causes opened(D) if available(D).

% Dynamic constraint: action a cannot be executed if atom H is true, where v and w are distinct:
f=v after a, if H.
f=w after a, if H.
This will make the program false, and is written shorthand with the keyword "nonexecutable":
nonexecutable a if H.
Examples:
% It is not permissible to drive a car if it has no gas.
nonexecutable driveCar if ~hasGas.
% It is not permissible to lift an object if it is heavy.
nonexecutable lift(object) if heavy(object).

% Dynamic law: By default, atom A is true after atom G (or conjunction of atoms G) is true:
default F after G.
Example:
default door(open) after door(unlocked).

In general, if something cannot be true, then we use "impossible" when writing the rules, but if instead we want to assert something is not true, then we use the negation(~). For example, if it is impossible for an object to be on the table and under it, we might write "impossible onTable(object) & underTable(object).", but express that if it rains outside the ground is not wet as "~groundWet if noRain".
Additionally, "impossible" is reserved only for fluents, while "nonexecutable" is only reserved for actions.

Here is an example representation.
Problem 1:
Given the following domain:
blocks: b1, b2, b3, b4.
locations: blocks + {table}
variables:
block: B, B1, B2.
loc: L, L1.
constants:
- loc(block) :: inertialFluent.
- in_tower(block) :: sdFluent.
- move(block, loc) :: action.

Represent the following constraints:
% 1. Two blocks cannot be at the same location.
% 2.1 A block is in a tower if it's location is on the table.
% 2.2 A block is in a tower if it's location is on something that is in a tower.
% 3. Blocks don't float in the air.
% 4. Moving a block causes it's location to move to loc.
% 5. The move action is not executable if something is on the location to be moved to.

Constraints:
% 1. Two blocks cannot be at the same location.
impossible loc(B1) = B & loc(B2) = B where B1\=B2.

% 2.1 A block is in a tower if it's location is on the table.
in_tower(B) if loc(B) = table.

% 2.2 A block is in a tower if it's location is on something that is in a tower.
in_tower(B) if loc(B) = B1 & in_tower(B1).

% 3. Blocks don't float in the air.
impossible ~in_tower(B).

% 4. Moving a block causes it's location to move to loc.
move(B,L) causes loc(B)=L.

% 5. The move action is permissible if something is on the location to be moved to.
nonexecutable move(B,L) if loc(B1) = B.

Problem 2:
Given the following domain:
<DOMAIN>

Write the following constraints:
<CONSTRAINTS>

Constraints:'''


# =============================================================================
# hanoi
# =============================================================================

hanoi_constraints = '''% 1. Two disks cannot be on the same disk.

% 2.1 A disk is in a tower if it's location is on the the peg a.
% 2.2 A disk is in a tower if it's location is on the the peg b.
% 2.3 A disk is in a tower if it's location is on the the peg c.

% 2.2 A disk is in a tower if it's location is on something that is in a tower.

% 3. Disks don't float in the air.

% 4. Moving a disk causes it's location to move to loc.

% 5. The move action is not executable if something is on the disk to be moved to.'''


hanoi_domain = ''':- sorts
        loc >> disk;
        loc >> peg.

:- objects
        a,b,c :: peg;
        d1,d2,d3 :: disk.

:- constants
        loc(disk)               :: inertialFluent(loc);
        in_tower(disk)  :: sdFluent;
        move(disk, loc):: action.

:- variables
        D, D1, D2       :: disk;
        L, L1           :: loc.
'''

hanoi_desc = '''To successfully stack disks in a tower, one needs to move disks off of other disks or pegs to achieve the desired ordered stack. Provide the relevant commonsense knowledge.'''

hanoi_semiformal_hint = '''There are three types of things: "loc", "disk", and "peg".
a,b, and c are pegs.
d1, d2, and d2 are disks. 

Fluents:
The (disk)'s location is an inertial fluent (loc).
A (disk) being in a tower is an inertial fluent.

Actions:
Moving a (disk) to a (loc) is an action. 
'''

hanoi_query = ''' % Initially, disk d1 is in disk d2 at time 0.
% Initially, disk d2 is on disk d3 at time 0.
% Initially, disk d3 is on peg a at time 0.

% Disk d3 is on disk d2 at time 6.
% Disk d2 is on disk d1 at time 6.
% Disk d1 is on peg c at time 6.'''


hanoi_program_full = '''
:- sorts
        loc >> room;
        gripper;
        ball;
        pickedup.

:- objects
        g1,g2 :: gripper;
        b1,b2,b3 :: ball;
        r1, r2, r3 :: room.

:- constants
        loc(ball) :: inertialFluent(room);
        ingripper(ball) :: inertialFluent;
        %in_room(ball,room) :: inertialFluent;
        pickedup(gripper, ball) :: inertialFluent;
        pickup(gripper, ball) :: action;
        release(gripper,ball) :: action;
        move(gripper, ball ,room) :: action.

:- variables
        B, B1, B2 :: ball;
        L, L1 :: loc;
        R :: room;
        G,G1,G2 ::gripper.


default ~ingripper(B).
default ~pickedup(G,B).

% picking up a ball

pickup(G,B) causes pickedup(G,B).

% moving a ball
move(G,B,R) causes loc(B) = R.

nonexecutable move(G,B,R) if ~pickedup(G, B).
nonexecutable pickup(G,B) if pickedup(G,B1) & B\=B1.

% releasing a ball
release(G,B) causes ~pickedup(G,B) if pickedup(G,B).


:- query
        label :: move;
        0: loc(b1) = r1 & loc(b2) = r1 & loc(b3) = r2;
        maxstep: loc(b1)=r3 & loc(b2) = r2 & loc(b3) = r3 & ~pickedup(G,b1) & ~pickedup(G,b2) & ~pickedup(G,b3).

'''


# =============================================================================
# gripper
# =============================================================================

gripper_domain = ''':- sorts
        loc >> room;
        gripper;
        ball;
        pickedup.

:- objects
        g1,g2 :: gripper;
        b1,b2,b3 :: ball;
        r1, r2, r3 :: room.

:- constants
        loc(ball) :: inertialFluent(room);
        ingripper(ball) :: inertialFluent;
        %in_room(ball,room) :: inertialFluent;
        pickedup(gripper, ball) :: inertialFluent;
        pickup(gripper, ball) :: action;
        release(ball,gripper) :: action;
        move( ball, gripper ,room) :: action.

:- variables
        B, B1, B2 :: ball;
        L, L1 :: loc;
        R :: room;
        G,G1,G2 ::gripper.
'''

gripper_constraints = '''% 1 Picking up a ball causes the ball to be picked up by the gripper.

% 2 Moving a ball with a gripper to a room causes the location to change to the room

% 3.1 The move action is not executable by a gripper if the ball is not already picked up from the gripper
% 3.2 The pickup action is not executable if gripper already has something picked up.

% 4. Releasing a ball with a gripper causes it to no longer be picked up by the gripper.'''

# =============================================================================
# logistics
# =============================================================================

logistics_domain = ''':- sorts
        location >> vehicle;
        object >> vehicle;
        vehicle >> truck;
        vehicle >> airplane;
        object >> package;
        city.

:- objects
        p1 :: package;
        city_1_1, city_1_2, city_2_1 :: location;
        t1 :: truck;
        city_1, city_2 :: city;
        a1 :: airplane.

:- variables
        O :: object;
        L, L1, L2 :: location;
        T :: truck;
        A :: airplane;
        V :: vehicle;
        P :: package;
        C, C1, C2 :: city.


:- constants
        inCity(location,city) :: inertialFluent;
        isAirport(location) :: inertialFluent;
        loc(object) :: inertialFluent(location);
        in(package, vehicle) :: inertialFluent;
        flyAirplane(airplane, location, location) :: action;
        driveTruck(truck,location,location,city) :: action;
        loadVehicle(package, vehicle) :: action;
        unloadVehicle(package, vehicle) :: action.'''

logistics_constraints = '''% 1.1 Driving a truck from one location to another in a city causes the location of the truck to change.
% 1.2 Driving a truck is not executable if the city of the two locations are not the same.
% 1.3 Driving a truck from a location is not executable if the truck\'s location is not the same as where it would be departing.

% 2.1 Flying an airplane from one location to another causes the location of the airplane to change.
% 2.2 Flying an airplane from a location is not executable if the location is not an airport.
% 2.3 Flying an airplane to a location is not executable if the locatino is not an airport.
% 2.4 Flying an airplane from a location is not executable if the plane is not in the location.

% 3.1 Loading a package in a vehicle causes the package to be in the vehicle.
% 3.2 Loading a package in a vehicle is not executable if the location of the package is not the same as the vehicle.
% 3.3 The location of a package is the same as the location of a vehicle, if the package is in the vehicle. 

% 4.1 Unloading a a package out of a vehicle causes the package to not be in it anymore.
% 4.2 Unloading a package from a vehicle is not executable if the package is not in the vehicle.'''


logistics_desc = '''A logistics problem consists of packages which are delivered by truck and/or airplane. Trucks can drive to locations in the same city, while airplanes can only fly to cities which have airports. Trucks and airplanes can be loaded/unloaded with packages.
Some things to consider are the requirements for succesfully driving or flying to a city and delivering a package.'''

logistics_query = '''% The package p1 is at city_1_1 at time 0. 
% The airplane a1 is in city_2_1 at time 1.
% The package was loaded at time step 3.'''

# =============================================================================
# satellites
# =============================================================================

satellites_domain = ''':- sorts
        satellite;
        instrument;
        direction;
        mode.

:- objects
        satellite0 :: satellite;
        instrument0 :: instrument;
        star0,groundstation1,groundstation2,phenomenon3,phenomenon4,star5,phenomenon6 :: direction;
        thermograph0,image1,spectrograph2 :: mode.

:- variables
        S :: satellite;
        I :: instrument;
        D,D1,D2 :: direction;
        M :: mode.

:- constants
        on_board(instrument,satellite) :: inertialFluent;
        supports(instrument,mode) :: inertialFluent;
        pointing(satellite, direction) :: inertialFluent;
        power_avail(satellite) :: inertialFluent;
        power_on(instrument) :: inertialFluent;
        calibrated(instrument) :: inertialFluent;
        have_image(direction,mode) :: inertialFluent;
        calibration_target(instrument,direction) :: inertialFluent;
        turn_to(satellite,direction,direction) :: action;
        switch_on(instrument,satellite) :: action;
        switch_off(instrument,satellite) :: action;
        calibrate(satellite,instrument,direction) :: action;
        take_image(satellite,direction,instrument,mode) :: action.'''

satellites_constraints = '''% 1.1 Turning a satellite to a direction from another direction causes it to be pointing to the new direction.
% 1.2 Turning a satellite to a direction from another direction causes it to no longer be pointing the previous direction.
% 1.3 Turning a satellite to a direction from another direction is not executable if it was not originally pointing at the original direction.

% 2.1 Switching on an instrument on a satellite causes the power of the instrument to be on.
% 2.2 Switching on an instrument on a satellite causes the instrument to not be calibrated.
% 2.3 Switching on an instrument on a satellite causes no power to be available on the satellite.
% 2.4 Switching on an instrument on a satellite is not executable if the instrument is not on board the satellite.

% 3.1 Switching off an instrument on a satellite causes the satellite to have available power.
% 3.2 Switching off an instrument on a satellite causes the power of the instrument to not be on.
% 3.3 Switching off an instrument on a satellite is not executable if the instrument is not on board the satellite.
% 3.4 Switching off an instrument on a satellite is not executable if the power of the power is not on.

% 4.1 Calibrating a satellite\'s instrument in a direction causes the instrument to be calibrated.
% 4.2 Calibrating a satellite\'s instrument in a direction is not executable if the instrument is not on the satellite.
% 4.3 Calibrating a satellite\'s instrument in a direction is not executable if the instrument\'s calibration target is no that direction.
% 4.4 Calibrating a satellite\'s instrument in a direction is not executable if the satellite is not pointing in that direction.
% 4.5 Calibrating a satellite\'s instrument in a direction is not executable if the power of the instrument is not on.

% 5.1 Taking an image from a satellite pointing in a direction with an instrument in some mode causes us to have the image in that direction and mode.
% 5.2 Taking an image from a satellite pointing in a direction with an instrument in some mode is not executable if the instrument is not calibrated.
% 5.3 Taking an image from a satellite pointing in a direction with an instrument in some mode is not executable if the instrument is not on board the satellite.
% 5.4 Taking an image from a satellite pointing in a direction with an instrument in some mode is not executable if the instrument does not support the mode.
% 5.5 Taking an image from a satellite pointing in a direction with an instrument in some mode is not executable if the instrument is not powered on.
% 5.6 Taking an image from a satellite pointing in a direction with an instrument in some mode is not executable if the satellite is not pointing in that direction.'''


# =============================================================================
# monkey and bananas
# =============================================================================

mnb_domain = ''':- sorts
    thing;
    location.
:- objects
    monkey,bananas,box :: thing;
    l1,l2,l3 :: location.
:- variables
    L :: location;
    B :: boolean.
:- constants
    loc(thing) :: simpleFluent(location);
    hasBananas,onBox :: simpleFluent;
    walk(location) :: action;
    pushBox(location) :: action;
    climbOn :: action;
    climbOff :: action;
    graspBananas :: action.'''
mnb_semiformal_hint = '''Each thing has a location
The monkey can have bananas
The monkey can be on the box

Actions:
walk to a location
push box to a location
climb on
climb off
grasp bananas'''

mnb_predicate_hint = '''Consider the following:

simple fluents: 
location of a thing must be a location.
hasBananas and onBox are simple fluents.

Actions:
walk (to a location)
push box (to a location)
climb on
climb off
grasp bananas'''

mnb_constraints = '''Write the following constraints:
% 1.1 The location of the bananas is where the monkey is if the monkey has bananas.
% 1.2 The location of the monkey is where the box is if the monkey is on the box.

% 2 Walking to a location causes the monkey’s location to change.

% 3.1 Walking is not permissible to a location if the monkey is already in that location
% 3.2  Walking is not permissible if the monkey is on the box.

% 4.1 Pushing the box to a location causes the location of the box to move.
% 4.2 Pushing the box to a location causes the location f the monkey to move.

% 5.1 Pushing the box is not permissible to a location if the monkey is at that location
% 5.2 Pushing the box is not permissible if the monkey is on the box.
% 5.3 Pushing the box is not permissible if the location of the monkey is not the same as the location of the box.

% 6 Climbing on the box causes the monkey to be on the box.

% 7.1 Climbing on the box is not permissible if the monkey is already on the box.
% 7.2 Climbing on the box is not permissible if the location of the monkey is not the same as the box.

% 8 Climbing off of the box causes the monkey to not be on the box.

% 9 Climbing off of the box is not permissible if the monkey is not on the box.

% 10.1 Grasping the bananas causes the monkey to have the bananas.
% 10.2 Grasping the bananas is not permissible if the monkey already has the bananas.
% 10.3 Grasping the bananas is not permissible if the monkey is not on the box.
% 10.4 Grasping the bananas is not permissible if the location of the monkey is not the same as the location of the bananas.

% 11.1 It is not permissible to both walk to a location and push the box to a location.
% 11.2 It is not permissible to both walk to a location and climb on the box.

% 12 It is not permissible to both push the box to a location and climb on the box.

% 13 It is not permissible to both climb off of the box and grasp the bananas.'''

mnb_desc = '''A monkey wants to get a bunch of bananas hanging from the ceiling. He can reach the bananas by first pushing a box to the empty place under the bananas and then climbing on top of the box.'''

mnb_query = '''% The monkey is at the box at time 0.
% The monkey has the bananas at time step 5.'''

# =============================================================================
# lifting
# =============================================================================

lifting_domain=''':- sorts
    end;
    height.

:- objects
  leftend, rightend    :: end;
  low, high            :: height.

:- variables
  X                    :: end.

:- constants
  level(end)           :: inertialFluent(height);
  onTable              :: inertialFluent;
  lift(end)            :: action.'''

lifting_constraints = '''% 1 Lifting an end causes the level of it to be high.

% 2 It is not permissible to lift an end if the end is already high.

% 3 The object is not on the table if the level of the left end is not equal to the right end.'''


lifting_desc = '''An object is on a table, but if the table ends are not equal then it will fall off. Provide the relevant commonsense knowledge.'''

lifting_semiformal_hint = '''There are two main types of things: "end" and "height".

leftend and rightend are ends.
low and high are heights.

Fluents:
The level of an (end) is an inertial fluent (height).
The object being on the table is an inertial fluent.

Actions:
Lift and (end).'''

lifting_query = '''% The object is on the table initially at time 0.
% The object is not on the table at time 1.'''



# =============================================================================
# shooting
# =============================================================================

# =============================================================================
# shooting_domain =''':- sorts
#   turkey >> turkey_.
# 
# :- objects
#   turkey1, turkey2    :: turkey_.
# 
# :- variables
#   T                   :: turkey.
# 
# :- constants
#   loaded,
#   alive(turkey)       :: inertialFluent;
#   target              :: inertialFluent(turkey+none);
#   load,
#   aim(turkey),
#   shoot               :: action.'''
# =============================================================================

shooting_domain =''':- sorts
    turkey_w_none >> turkey.

:- objects
  turkey1, turkey2    :: turkey.

:- variables
  T                   :: turkey.

:- constants
  loaded,
  alive(turkey)       :: inertialFluent;
  target              :: inertialFluent(turkey+none);
  load,
  aim(turkey),
  shoot               :: action.'''



shooting_constraints = '''% 1.1 Loading the gun causes it to be loaded.
% 1.2 Loading the gun causes the target to be “none”.

% 2 Aiming at something makes it a target.

% 3.1 Shooting causes something to not be alive if it is the target.
% 3.2 Shooting causes the gun to not be loaded.

% 4.1 It is not permissible to shoot if the gun is not loaded.
% 4.2 It is not permissible to both aim and shoot.oth aim and shoot. '''

shooting_desc = '''To perform the task of shooting a turkey, one needs to load, aim, and finally shoot the gun while aiming at the turkey. Provide the relevant commonsense knowledge.
Some things to consider are the requirements for successfully shooting a turkey, and the effects of shooting it.'''


shooting_semiformal_hint_old = '''The gun can be loaded
The turkey can be alive
The target can be the turkey

Actions:
load the gun
aim the gun at the (turkey)
shoot the gun'''

shooting_semiformal_hint = '''There is one type of thing: "turkey".

t1 and t2 are turkeys.

Fluents
The gun being loaded is a inertial fluent (boolean).
The (turkey) being alive is an inertial fluent.
The target is an inertial fluent (turkey).


Loading the gun is an action.
Aiming at a (turkey) is an action.
Shooting is an action.

Actions:
load the gun
aim the gun at the turkey
shoot the gun'''

shooting_predicate_hint = '''Consider the following:

inertial fluents: 
The turkey can be alive.
The target .

Actions:
walk (to a location)
push box (to a location)
climb on
climb off
grasp bananas'''



shooting_query = '''% The gun is unloaded at time step 3.

% The turkey is alive at time step 1.'''

# =============================================================================
# switches
# =============================================================================


switches_domain = ''':- sorts
        switch;
        switch_direction.

:- objects
        s1,s2 :: switch;
        up,down ::switch_direction.

:- variables
        S,S1,S2 :: switch;
        D :: switch_direction.

:- constants
        status(switch) :: inertialFluent(switch_direction);
        flip(switch) :: action.'''

switches_constraints = '''% 1. By default, the status of a switch is the same.

% 2.1 Flipping a switch causes the status of the switch to change to up if it was down.
% 2.2 Flipping a switch causes the status of the switch to change to down if it was up.

% 3 It is impossible for the status of both switches to be up.'''

switches_desc = '''Two light switches can each be flipped, but only one can be on at a time.'''


switches_query = '''% The switch s1 is on at time step 0.
% The switch s2 is on at time step 3.'''



switches_semiformal_hint = '''There are tqo main types of things: "switch" and "switch_direction".

s1 and s2 are switches.
up and down are switch directions.

Fluents:
A (switch)'s status is an inertial fluent (switch_direction).

Actions:
Flip a (switch)'''




# =============================================================================
# ferry
# =============================================================================

ferry_domain_old= ''':- sorts
	int;
	type.

:- macros
	NUM -> 10;
	CAPACITY -> 4.

:- objects
	0..NUM :: int;
	sheep, wolf :: type;
    .

:- constants
	cross(int, int) :: exogenousAction;
	here(type) :: inertialFluent(int);
	boat_here :: inertialFluent.

:- variables
	Sheep, Sheep_here, Sheep_new :: int;
	Wolves, Wolves_here, Wolves_new :: int;
	N, N1 :: int.'''

ferry_domain= ''':- sorts
	int;
	type.

:- objects
	0,1,2,3,4,5,6,7,8,9,10 :: int;
	sheep, wolf :: type;
    10 :: num;
    4 :: capacity.

:- constants
	cross(int, int) :: action;
	here(type) :: inertialFluent(int);
	boat_here :: inertialFluent.

:- variables
	Sheep, Sheep_here, Sheep_new :: int;
	Wolves, Wolves_here, Wolves_new :: int;
	N, N1 :: int.'''

ferry_constraints = '''
% 1.1 don't cross with more sheep than still here
% 1.2 don't cross with more wolves than still here


% 2.1 don't cross when boat is not here and there are more than num sheep
% 2.2 don't cross when boat not here and there are more than num wolves

% 3. don't cross with an empty boat

% 4. don't cross with more than the maximum capacity of animals

% 5.1 crossing causes the boat to not be here if it was here
% 5.2 crossing causes the boat to be here if it was not here

% 6.1 crossing causes the number of sheep here to be the number of sheep here minus the number of sheep crossing if the boat is here
% 6.1 crossing causes the number of wolves here to be the number of wolves here minus the number of wolves crossing if the boat is here

% 7.1 crossing causes the number of sheep here to be the number of sheep here plus the number of sheep crossing if the boat is not here
% 7.2 crossing causes the number of wolves here to be the number of wolves here plus the number of wolves crossing if the boat is not here

% 8.1 don't allow less sheep than wolves when sheep are still here
% 8.2 don't allow less wolves than sheeps when there are less than N sheeps here'''



# =============================================================================
# Sudoku
# =============================================================================

# =============================================================================
# sudoku_domain = ''':- sorts
#     int.
# 
# :- objects
#         0,1,2,3,4,5,6,7,8 :: int.
# 
# :- constants
#         element(int,int) :: inertialFluent(int).
# :- variables
#         Row, Row1, Column, Column1, Num, Num1 :: int.
# 
# '''
# 
# sudoku_constraints = '''% 1. Two elements with the same row and column cannot have different numbers
# 
# % 2. Two elements with the same row and same number cannot have a different column
# 
# % 3. Two elements with the same column and number cannot have a different row
# 
# % 4.1 Two elements that are in the same grid box (denoted by floor division for 9x9 Sudoku), have the same number, but different row values is not permissible.
# % 4.2 % 4.1 Two elements that are in the same grid box (denoted by floor division for 9x9 Sudoku), have the same number, but different column values is not permissible.
# 
# 
# '''
# =============================================================================
sudoku_domain = ''':- sorts
    int.

:- objects
        0,1,2,3,4,5,6,7,8 :: int.

:- constants
        element(int,int) :: inertialFluent(int).
:- variables
        Row, Row1, Column, Column1, Num, Num1 :: int.

'''

sudoku_constraints = '''% 1. The same number cannot appear twice in the same row.
% 2. The same number cannot appear twice in the same column.
% 3. The same number cannot appear twice in the 3x3 box. (You can use division / to check if 2 cells are in the same box.)'''

# =============================================================================
# Logic puzzle sample
# =============================================================================

logic_puzzle_domain = '''

:- sorts
    person;
    pay;
    wine.


:- objects
    priscilla, kurt, isabel, robin :: person;
    24, 25, 26, 27 :: pay;
    chianti, port, riesling, shiraz :: wine.

:- constants
    paid(person) :: inertialFluent(pay);
    had(person) :: inertialFluent(wine).
:- variables
    Person,Person1,Person2 :: person;
    Pay,Pay1,Pay2 :: pay;
    W,W1,W2 :: wine.
    
'''

logic_puzzle_constraints = '''1. The person who had the port paid 1 dollar more than Kurt.
2.1 The person who paid $25 and the person who paid $24 are different.
2.2 The person who paid $25 was Priscilla or had the shiraz.
2.3 The person who paid $24 was Priscilla or had the shiraz.
3.1 The person who paid $27 and Priscilla are different.
3.2 The person who paid $27 had the chianti or had the port.
3.3 Priscilla had the chianti or had the port.
4. Isabel paid $25.'''


logic_puzzle_constraints = '''The local foodie club met at Chez Martin last night for their monthly meal. Match each person to their choice of wine and entree, and determine how much each owed at the end of the night. Remember, as with all grid-based logic puzzles, no option in any category will ever be used more than once.
1. The person who had the port paid 1 dollar more than Kurt.
2. Of the person who paid $25 and the person who paid $24, one was Priscilla and the other had the shiraz.
3. Of the person who paid $27 and Priscilla, one had the chianti and the other had the port.
4. Isabel paid $25.'''

'''
paid(Person)=Pay+1 if choice(Person) = port & paid(Kurt)=Pay.

paid(Person)=25 & paid(Person1)=24.




'''

'''

1. The person who had the port paid 1 dollar more than Kurt.
2.1 The person who paid $25 and the person who paid $24 are different.
2.2 The person who paid $25 was Priscilla or had the shiraz.
2.3 The person who paid $24 was Priscilla or had the shiraz.
3.1 The person who paid $27 and Priscilla are different.
3.2 The person who paid $27 had the chianti or had the port.
3.3 Priscilla had the chianti or had the port.
4. Isabel paid $25.


'''
'''

1. The person who had the port paid 1 dollar more than Kurt.
2.1 The person who paid $25 and the person who paid $24 are different.
2.2 The person who paid $25 was Priscilla or had the shiraz.
2.3 The person who paid $24 was Priscilla or had the shiraz.
3.1 The person who paid $27 and Priscilla are different.
3.2 The person who paid $27 had the chianti or had the port.
3.3 Priscilla had the chianti or had the port.
4. Isabel paid $25.


'''



problem_dict = {'lifting': [lifting_domain,lifting_constraints, lifting_desc, lifting_query, lifting_semiformal_hint],
             'monkey':[mnb_domain,mnb_constraints, mnb_desc, mnb_query],
             'shooting':[shooting_domain,shooting_constraints, shooting_desc, shooting_query, shooting_semiformal_hint],
             'satellites':[satellites_domain,satellites_constraints],
             'logistics':[logistics_domain,logistics_constraints, logistics_desc, logistics_query],
             'gripper':[gripper_domain,gripper_constraints],
             'hanoi':[hanoi_domain,hanoi_constraints, hanoi_desc, hanoi_query, hanoi_semiformal_hint],
             'switches':[switches_domain,switches_constraints, switches_desc,switches_query, switches_semiformal_hint],
             'ferry':[ferry_domain, ferry_constraints],
             'sudoku':[sudoku_domain, sudoku_constraints],
             'lp' :[logic_puzzle_domain,logic_puzzle_constraints]
             }



