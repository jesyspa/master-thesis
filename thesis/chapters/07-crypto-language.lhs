\chapter{A Language for Cryptography}
\label{chp:language}

So, the stuff we describe in chapters 2-4 can nicely prove things about simple
games, and the stuff we describe in chapters 5-6 can allow us to impose much
more powerful constraints on games (and express more complex games), but all
together they create a system where getting anything done involves writing a lot
of code, most of it boilerplate.

In a sense, the problem is that our descriptions of games are not syntactic
enough: the free monad lets us syntactically store what operations are
performed, but they are still related by binds with arbitrary Agda code
inbetween.  We want to work on the syntax tree of the game itself, and then
things like bounds on the number of adversary calls can be written automatically
for many cases.

So we either want to use reflection or we want to write a separate language and
compile from that into the Agda system we describe.  In this chapter, I'd like
to say some things about the design of such a language.

I don't actually know what things yet, but it's an interesting topic and I think
it would be a fitting way to conclude the work.
