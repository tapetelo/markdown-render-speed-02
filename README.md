# markdown-render-speed-02

`parse.js` is a from-scratch, dependency-free Markdown renderer. It
produces byte-for-byte the same HTML as marked 18.1.3 with default
options (GFM enabled) on the competition's practice cases, while doing
less work: a hand-written block scanner and inline scanner replace the
regex-heavy passes, with fast paths for plain paragraphs and plain text
runs.

make.fun bounty entry for "Make Markdown rendering faster" by @tapetelo.
