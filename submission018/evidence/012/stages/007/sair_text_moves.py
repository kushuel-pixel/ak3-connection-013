"""Independent text-word replay for the fourteen SAIR moves."""

def encode(state):
    letters = {-2: "Y", -1: "X", 1: "x", 2: "y"}
    return tuple("".join(letters[a] for a in row) for row in state)


def reduce(block):
    result = []
    for letter in block:
        if result and result[-1].swapcase() == letter:
            result.pop()
        else:
            result.append(letter)
    return "".join(result)


def move(state, m):
    if m < 2:
        i = m
    elif m < 6:
        i = (m - 2) // 2
    else:
        i = (m - 6) // 4
    word = state[i]
    alt = state[1 - i]
    if m < 2:
        out = word.swapcase()[::-1]
    elif m < 6:
        out = reduce(word + (alt if m % 2 == 0 else alt.swapcase()[::-1]))
    else:
        ch = "xXyY"[(m - 6) % 4]
        out = reduce(ch + word + ch.swapcase())
    return (out, alt) if i == 0 else (alt, out)


def height(state):
    return len(state[0]) + len(state[1])
