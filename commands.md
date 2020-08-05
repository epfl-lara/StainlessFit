
### Rebuild stainlessfit
sbt cli/universal:stage

### Run an example for evaluation
cli/target/universal/stage/bin/fit eval --bench examples/eval/list_perf.sf
