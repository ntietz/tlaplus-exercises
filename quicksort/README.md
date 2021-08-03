This is a basic check of quicksort in TLA+.

To run it, I assume you have some scripts setup on your path; one version of these is [here](https://github.com/pmer/tla-bin), but they're pretty simple wrappers around the tlatools JAR.

Now to run it:
```
tlc quicksort.tla

# Or with multiple workers
tlc -workers 4 quicksort.tla
```

As far as I can tell right now, there's not a great way to override constants, so if you want to test with different values, edit the .cfg file directly.
