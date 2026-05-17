# The Friends and the Window Story

*[Bridges →](bridges.md)*

---

## Cluster

- [The Friends and the Window Story](world.md) — what the architecture commits to about the world, and what it leaves to whoever is using it *(you are here)*
- [The Wall and the Phone Story](bridges.md) — how facts in the world become problems in the kernel
- [Witnessing](witnessing.md) — what the architecture is willing to certify, and what it leaves open

---

## Same window, two answers

Two friends are texting about meeting up at the park.

One asks: *is it nice out?*

The other looks out the window. Overcast sky. Dry pavement. Fifteen degrees on the thermometer by the kitchen door. No wind to speak of.

There is one world here. One sky, one actual temperature, one actual wind. Whatever the weather is, it is what it is, and neither friend is going to change it by texting back.

But the two friends are not asking the same question even though they are using the same word. The one who asked has been planning to sit in the grass for an hour and means *warm enough to be outside without a jacket*. The one looking out the window has been getting drenched all week and means *not raining right now*. Same word, two different things underneath it.

The first friend would call fifteen-and-overcast not nice. The second would call it fine. They are both right about what they meant. They are not right about the same question.

Now imagine someone trying to settle this from the outside. Some authority who is going to issue a verdict on what the weather is *really* like, in some absolute sense. They have to pick between the two meanings of *nice*. Whichever way they go, one of the friends will be told their question wasn't really their question.

The architecture's posture is to refuse that role.

---

## What the architecture is doing here

The architecture has a slot in it for the predicate that says what is true about the world. The first friend's *nice* fills the slot one way. The second friend's *nice* fills it another way. Both fillings produce something the architecture can do its work over. The architecture does not say which one of them is the right meaning of *nice*. It says: *whichever you supply, the rest of what I do still goes through.*

This is the load-bearing piece of the world layer, and the friends scene is exactly the case it is built for. Two fillings, both legitimate, and an architecture that does not pick between them.

A working one-line definition:

> **The world layer is the slot the architecture leaves for whatever is true. Filling the slot is the application's job. The architecture's claims hold across whatever filling the application supplies, as long as the filling has the right shape.**

The bubble layer holds the claims. The agent layer carries the names that act on those claims. The world layer is the slot for the place those claims are about.

---

## Why a slot, and not a story

You could imagine an architecture that took a different posture. There are two natural alternatives, and they fail in opposite directions.

The first alternative is to leave the truth predicate unsaid. Just say "the architecture handles lies correctly" and let the reader fill in what a lie *is* on their own. This breaks down the moment a theorem needs to mention the truth. A lie is a thing somebody says that doesn't match the truth. If the truth is unsaid, *not matching the truth* is unsaid. The theorem about lies stops meaning anything in particular. Every theorem that mentions the world inherits the same vagueness, and "the architecture handles X correctly" becomes a sentence with nothing under it.

The second alternative is to fix the truth predicate by fiat. Just declare "the world is such-and-such" inside the architecture. This makes the theorems sharp again — but it also makes them claims about the world that the architecture cannot actually back. The architecture has no special access to which world its readers are sitting in. A reader whose world is different now has to either argue with the architecture or throw it out. The first alternative was too vague to use; the second is too presumptuous to be used by anyone the author didn't have in mind.

The slot is the move that closes both at once. It says: there is a place for a truth predicate in here, and you are the one who fills it. Once you fill it, the theorems are sharp. Until you fill it, the theorems are conditionals waiting for their parameter. Either way, the architecture does not pretend to know what is true.

The friends scene is what makes this concrete. Both friends fill the slot legitimately because they are not evaluating the same predicate. One supplies *nice-for-sitting-in-the-park*; the other supplies *nice-as-in-not-raining.* The architecture can reason over either filling, but it does not collapse them into one proposition. Neither has to argue with the architecture to do so. The architecture's results about lies, about checking, about partial observation come out the same way for both, by the same proofs, with each friend's own *nice* substituted in.

---

## What the architecture is not doing

The slot framing is sometimes mistaken for two stronger things, and it is worth being clear about both.

It is not a guarantee that the filling someone supplies is *faithful* to the world they are in. If the first friend filled the slot with *nice means warm enough for the park* and then went outside in fifteen-and-overcast and was miserable, that is information about whether the meaning fits her actual situation, not about whether the architecture did its job. The architecture's job is not to certify that the filling is faithful. Once the slot is filled, the architecture can reason over that filling; whether the filling was the right one for the actual situation remains the application's responsibility.

It is also not a stance on what the world *is*, in the deeper sense. The slot has a shape — it expects a truth predicate, an observation function, a notion of how much it costs to verify something — and beyond that, the architecture stays out of the metaphysics. A reader who thinks of worlds as physical states, a reader who thinks of them as possible-worlds points, a reader who thinks of them as model-theoretic structures, and a reader who has not made up their mind can all fill the slot. The architecture's results do not depend on which of these the reader has in mind.

Both of these are sometimes read as the architecture dodging its responsibilities. They are not. They are the architecture being clear about which responsibilities are its and which belong to whoever is using it. The slot is what makes the line drawable.

---

## Same window, more than one shape of weather

There is a second thing the friends scene shows, and it gets clearer if you change the weather.

Suppose it is not fifteen and overcast. Suppose the sky is split — sun in one half, dark cloud in the other — and the wind is gusting. The first friend, the park-and-grass one, looks at the sky and decides it is going to rain. The second friend, the not-currently-raining one, observes that it is not currently raining. They text again. Now they are disagreeing about a different thing: not what *nice* means, but what is going to happen.

The world has changed shape, in a sense the architecture cares about. With a steady overcast and a steady fifteen, neither friend is misled by what they can see; the disagreement is purely about the meaning of the question. With a split sky, what each friend can see from where they are leaves room for a future that goes either way, and they end up with different working answers because their viewpoints catch different parts of the same scene.

This is the world having more shape than just *truth*. The architecture's slot has room for it. There is room for the fact that some questions cost effort to settle, room for the fact that two situations can look the same from where you are standing while disagreeing on what is true, room for the fact that what an agent says is something they choose to do regardless of whether it is true. The architecture does not decide whether your weather is steady-and-overcast or split-and-gusty. It does decide what extra structure to make available *in case* your weather has more shape.

The structure that makes the world's shape into something the architecture can use is the subject of the next file.

---

## Takeaway

The architecture leaves a slot for what is true, and lets whoever is using it fill the slot. Two friends with two genuinely different ideas of what *nice weather* means can both fill the slot legitimately, and the architecture's results hold across both fillings, by the same proofs.

This posture costs the architecture the ability to say anything about what is *actually* true in the actual world. It buys, in exchange, the ability to be used by readers whose worlds, meanings, and metaphysics differ — without any of them having to renegotiate what the architecture claims. The slot is the dividing line: the architecture stops where the slot begins, and the application picks up where the slot is filled.

The world can also have more shape than just truth — costs to checking, situations that look alike from where the observer is, things people can say regardless of the truth. The next file, [bridges](bridges.md), is about how those shapes get from the world side into the kernel without becoming the kernel's claims about what the world is like.

---

*[Bridges →](bridges.md)*

---

*Proof-side companion: [../../DOCS/architecture/WORLD.md](../../DOCS/architecture/WORLD.md).*
