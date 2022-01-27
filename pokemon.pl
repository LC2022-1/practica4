/*
Model pokemons using logical statements.
*/

/* Registered pokemons */
pok(bulbassaur).
pok(ivysaur).
pok(venusaur).
pok(charmander).
pok(charmeleon).
pok(charizard).
pok(squirtle).
pok(wartortle).
pok(blastoise).
pok(caterpie).
pok(metapod).
pok(butterfree).
pok(pidgey).
pok(geodude).
pok(onix).
pok(staryu).
pok(starmie).

/* Registered pokemon types */
type(normal).
type(fire).
type(water).
type(electric).
type(grass).
type(ice).
type(fighting).
type(poison).
type(ground).
type(flying).
type(psychic).
type(bug).
type(rock).
type(ghost).
type(dragon).

/* All pokemons have at least one type */
pok_type(pok(bulbassaur), type(grass)).
pok_type(pok(bulbassaur), type(poison)).
pok_type(pok(ivysaur), type(grass)).
pok_type(pok(ivysaur), type(grass)).
pok_type(pok(venusaur), type(poison)).
pok_type(pok(venusaur), type(poison)).

pok_type(pok(charmander), type(fire)).
pok_type(pok(charmeleon), type(fire)).
pok_type(pok(charizard), type(fire)).
pok_type(pok(charizard), type(flying)).

pok_type(pok(squirtle), type(water)).
pok_type(pok(wartortle), type(water)).
pok_type(pok(blastoise), type(water)).

pok_type(pok(caterpie), type(bug)).
pok_type(pok(metapod), type(bug)).
pok_type(pok(butterfree), type(bug)).
pok_type(pok(butterfree), type(flying)).

pok_type(pok(pidgey), type(flying)).
pok_type(pok(pidgey), type(normal)).

pok_type(pok(onix), type(rock)).
pok_type(pok(onix), type(ground)).

pok_type(pok(geodude), type(ground)).
pok_type(pok(geodude), type(rock)).

pok_type(pok(staryu), type(water)).
pok_type(pok(starmie), type(water)).
pok_type(pok(starmie), type(psychic)).

/* Some pokemons evolve into another pokemon */
pok_evolves_to(pok(bulbassaur), pok(ivysaur)).
pok_evolves_to(pok(ivysaur), pok(venusaur)).

pok_evolves_to(pok(charmander), pok(charmeleon)).
pok_evolves_to(pok(charmeleon), pok(charizard)).

pok_evolves_to(pok(squirtle), pok(wartortle)).
pok_evolves_to(pok(wartortle), pok(blastoise)).

pok_evolves_to(pok(caterpie), pok(metapod)).
pok_evolves_to(pok(metapod), pok(butterfree)).

pok_evolves_to(pok(starmie), pok(staryu)).

/*
 A pokemon is ancestor of another if it can evolve (in one or more
 steps) into the other. */
%?- pok_is_ancestor_to(pok(bulbassaur), X).
%@    X = pok(ivysaur)
%@ ;  X = pok(venusaur)
%@ ;  false.
pok_is_ancestor_to(pok(_), pok(_)) :- false.

/*
 At the beginning, only three pokemons are available. They are starter
 pokemons.
 */
starter(pok(bulbassaur)).
starter(pok(charmander)).
starter(pok(squirtle)).

/*
 A starter team is a team containing a pokemon that is a starter pokemon
 or one that has evolved from one. */
%?- starter_team([pok(pidgey), pok(venusaur)]).
%@    true
%@ ;  false.
%
%?- starter_team([pok(onix), pok(caterpie)]).
%@ false.
starter_team([pok(_) | _]) :- false.

/*
 During pokemon battles, the type of the pokemons determines the
 effectiveness of the attack. There are four basic kinds of effect.
*/
eff(no_effect).
eff(not_very).
eff(normal).
eff(super).

/*
  An attack of a type affects pokemons of other type with a given effect.
*/
type_affects_type(type(water), eff(super), type(ground)).

type_affects_type(type(ground), eff(normal), type(water)).

type_affects_type(type(normal), eff(not_very), type(rock)).
type_affects_type(type(normal), eff(no_effect), type(ghost)).
type_affects_type(type(normal), eff(normal), type(Y)) :-
    dif(Y, rock),
    dif(Y, ghost).

/*
  Effects can be ordered. That is, an attack that has no effect can be
  considered weaker than an attack that is not very effective.
*/
eff_succ(eff(no_effect), eff(not_very)).
eff_succ(eff(not_very), eff(normal)).
eff_succ(eff(normal), eff(super)).

/*
  Extends the effect order to be a transitive relation. */
%?- eff_ord(eff(no_effect), X).
%@    X = eff(not_very)
%@ ;  X = eff(normal)
%@ ;  X = eff(super)
%@ ;  false.
eff_ord(eff(_), eff(_)) :- false.

/*
 A pokemon A of a certain type can beat another pokemon B if A has an effect
 advantage. That is, if the effect of type A over type B is stronger than the
 effect of type B over type A.*/
%?- pok_beats_pok(pok(starmie), X).
%@    X = pok(onix)
%@ ;  X = pok(geodude)
%@ ;  false.
pok_beats_pok(pok(_), pok(_)) :- false.

/*
 In a battle, pokemons go one to one. A team beats another if every pokemon
 battle results in a victory.
 */
%?- team_beats_team([pok(starmie), pok(staryu)], X).
%@    X = []
%@ ;  X = [pok(onix)]
%@ ;  X = [pok(onix),pok(onix)]
%@ ;  X = [pok(onix),pok(geodude)]
%@ ;  X = [pok(geodude)]
%@ ;  X = [pok(geodude),pok(onix)]
%@ ;  X = [pok(geodude),pok(geodude)]
%@ ;  false.
team_beats_team(_, []) :- false.
team_beats_team([pok(_) | _], [pok(_) | _]) :- false.

/* Registered pokemon trainers */
trainer(brock).
trainer(misty).

/* Pokemon trainers have a pokemon team */
team(trainer(brock), [pok(geodude), pok(onix)]).
team(trainer(misty), [pok(starmie), pok(staryu)]).

/*
 A given team can defeat a pokemon trainer. That is, it can defeat its
 pokemon team.
 */
%?- team_beats_trainer(X, trainer(brock)).
%@    X = [pok(squirtle),pok(squirtle)|_A]
%@ ;  X = [pok(squirtle),pok(wartortle)|_A]
%@ ;  X = [pok(squirtle),pok(blastoise)|_A]
%@ ;  X = [pok(squirtle),pok(staryu)|_A]
%@ ;  X = [pok(squirtle),pok(starmie)|_A]
%@ ;  X = [pok(wartortle),pok(squirtle)|_A]
%@ ;  X = [pok(wartortle),pok(wartortle)|_A]
%@ ;  X = [pok(wartortle),pok(blastoise)|_A]
%@ ;  X = [pok(wartortle),pok(staryu)|_A]
%@ ;  X = [pok(wartortle),pok(starmie)|_A]
%@ ;  X = [pok(blastoise),pok(squirtle)|_A]
%@ ;  X = [pok(blastoise),pok(wartortle)|_A]
%@ ;  X = [pok(blastoise),pok(blastoise)|_A]
%@ ;  X = [pok(blastoise),pok(staryu)|_A]
%@ ;  X = [pok(blastoise),pok(starmie)|_A]
%@ ;  X = [pok(staryu),pok(squirtle)|_A]
%@ ;  X = [pok(staryu),pok(wartortle)|_A]
%@ ;  X = [pok(staryu),pok(blastoise)|_A]
%@ ;  X = [pok(staryu),pok(staryu)|_A]
%@ ;  X = [pok(staryu),pok(starmie)|_A]
%@ ;  X = [pok(starmie),pok(squirtle)|_A]
%@ ;  X = [pok(starmie),pok(wartortle)|_A]
%@ ;  X = [pok(starmie),pok(blastoise)|_A]
%@ ;  X = [pok(starmie),pok(staryu)|_A]
%@ ;  X = [pok(starmie),pok(starmie)|_A]
%@ ;  false.
team_beats_trainer(_, trainer(_)) :- false.
