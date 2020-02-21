## StainlessFit [![Build Status][larabot-img]][larabot-ref]

### Stainless Built Following System FR Type System

This project works to formalize the proof obligation checking of [Stainless](https://stainless.epfl.ch/).
It is a natural follow-up to the System FR from https://arxiv.org/abs/1904.03482.


### Installation

Run `sbt cli/universal:stage` to get a binary in folder `cli/target/universal/stage/bin`.

Then, after making a symbolic link or referring to the binary directly, you can
type-check an example using:

```
fit typecheck --html examples/typechecker/stream.sf
```

This will create an HTML file of the type-checking derivation in `examples/typechecker/stream.sf.html`.

### Syntax coloring

Syntax coloring mode is not yet available.
If you are using [emacs](https://www.gnu.org/software/emacs/),
you can try to use [tuareg-mode](https://github.com/ocaml/tuareg) for
approximate syntax coloring.

[larabot-img]: http://laraquad4.epfl.ch:9000/epfl-lara/StainlessFit/status/master
[larabot-ref]: http://laraquad4.epfl.ch:9000/epfl-lara/StainlessFit/builds
