# Cordial

A EDSL to describe *System-on-Chip* (SoC) Architectures.

This work is a public alpha of the system as it stands.

Modern Systems-on-a-Chip (SoC) are constructed by composition of IP (Intellectual Property) cores.
The communication between IP Cores are governed by well described interaction protocols.
However, there is a disconnect between the machine readable specification of these protocols and the verification of their implementation in known hardware description languages.
Although tools can be written to address such a separation of concerns, such tooling is often hand written and used to check hardware designs *a posteriori*.
We have developed a dependent type-system and proof-of-concept modelling language to reason about the physical structure of hardware interfaces respective to user provided descriptions.
Our type-system provides correct-by-construction guarantees that the interfaces on an IP Core will be well-typed if they adhere to a specified standard.


Cordial comprises of a system of related statically typed models that reason about the structure of interfaces on a component respective to a given interface specification.
We build upon existing work from existing hardware description tooling, and utilise state-of-the-art concepts from programming language theory to provide correct-by-construction guarantees over construction of abstract interface descriptions and the adherence of concrete interfaces to said abstract descriptions.
The framework has been realised within the dependently typed language Idris [^1] as a proof-of-concept implementation, and it has been used to describe several well known IP communication protocols.
Namely: APB, LocalLink, and AXI3/4.

This work is constantly in progress and as such documentation may not be as readily available or polished as we would like.
Any questions or comments then please do get in touch.

[^1]: https://www.idris-lang.org
