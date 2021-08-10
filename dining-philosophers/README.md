This is a basic implementation of [Dining Philosophers](https://en.wikipedia.org/wiki/Dining_philosophers_problem) in TLA+ / PlusCal.

To run it, I assume you have some scripts setup on your path; one version of these is [here](https://github.com/pmer/tla-bin), but they're pretty simple wrappers around the tlatools JAR.

Now to run it:
```
tlc <SPEC>.tla

# Or with multiple workers
tlc -workers 4 <SPEC>.tla
```

There are three specs:
* `deadlock.tla` demonstrates that the naive approach here (pick up the left one, then pick up the right one) results in a deadlock.
* `livelock.tla` demonstrates that if you just let philosophers do whatever they want and pick up any fork that's available to them, but require they drop them if they can't get _all_ their forks, it ends with a livelock.
* `diningphilosophers.tla` demonstrates that if you rule the philosophers with an iron fist and demand they get their forks in a particular order (and wait, if they're not available, dammit!) then all is fine and everyone gets to eat.
