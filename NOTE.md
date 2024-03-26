# Note

## Nodes

- FALSE and TRUE are node index 0 and 1 respectively with `level: INVALID_LEVEL
(2147483647)`
- After FALSE&TRUE, The next consecutive nodes are var and nvar of variables.
- Other nodes are initialized as `level: INVALID_LEVEL, ref_cnt: 0`
- There are 5 types of nodes:
  - Constant: TRUE/FALSE
  - Variable: var/nvar
  - Referenced: directly referenced nodes
  - Intermediate: occupied but not directly referenced nodes, MAY or MAY NOT be
  cleaned up in next GC
  - Free: free nodes

## Secrets

- Node with `level: INVALID_LEVEL` are either TRUE/FALSE or free nodes.
