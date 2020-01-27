## StainlessFit [![Build Status][larabot-img]][larabot-ref]

### Foundational Stainless

This project works to formalize the proof obligation checking of [Stainless](https://stainless.epfl.ch/).
It is a natural follow-up to the System FR from https://arxiv.org/abs/1904.03482.


### Installation

Run `sbt universal:stage` to get a binary in folder `cli/target/universal/stage/bin`.

Then, after making a symbolic link or referring to the binary directly, you can
type-check an example using:

```
stainlessfit-cli typecheck --html examples/streams.sc
```

This will create an HTML file of the type-checking derivation in `examples/streams.sc.html`.

[larabot-img]: http://laraquad4.epfl.ch:9000/epfl-lara/StainlessFit/status/master
[larabot-ref]: http://laraquad4.epfl.ch:9000/epfl-lara/StainlessFit/builds
