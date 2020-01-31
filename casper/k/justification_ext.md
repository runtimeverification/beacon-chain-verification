Basic Justification Properties
==============================


```k

requires "justification.k"

module JUSTIFICATION-EXT 

    imports JUSTIFICATION

```

- Supermajority property 

```k
    rule
    <k> apply("supermajority_weaken") => . ... </k>
    <g> (VS1 <= VS2) and superMajorityLink(VS1, S, T, SH, TH) 
        => superMajorityLink(VS2, S, T, SH, TH)
    </g>
```

```k
endmodule

```
