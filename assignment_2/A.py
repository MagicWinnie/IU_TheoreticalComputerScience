# Dmitriy Okoneshnikov
from copy import deepcopy
from pprint import pprint
from string import ascii_letters
from typing import List, Tuple, Dict, Set


def isalnum(s: str) -> bool:
    """Check if string contains only latin letters and digits.

    Args:
        s (str): string to check.

    Returns:
        bool: whether the string contains only latin letters and digits.
    """
    for el in s:
        if not el.isdigit() and el not in ascii_letters:
            return False
    return True


def check_lines(lines: List[str]) -> None:
    """Check if the necessary variables are in input.

    Args:
        lines (List[str]): List containing a variable on each line.
    """
    assert len(lines) == 5,\
        "Input file should contain 5 variables: states, alpha, initial, accepting, and trans!"
    assert lines[0].startswith("states=["),\
        "Input file should contain variable `states`!"
    assert lines[1].startswith("alpha=["),\
        "Input file should contain variable `alpha`!"
    assert lines[2].startswith("initial=["),\
        "Input file should contain variable `initial`!"
    assert lines[3].startswith("accepting=["),\
        "Input file should contain variable `accepting`!"
    assert lines[4].startswith("trans=["),\
        "Input file should contain variable `trans`!"


def parse_lines(lines: List[str]) ->\
        Tuple[List[str], List[str], List[str], List[str], List[str]]:
    """Parse lines of input.

    Args:
        lines (List[str]): List containing a variable on each line.

    Returns:
        List[str]: states variable.
        List[str]: alpha variable.
        List[str]: initial variable.
        List[str]: accepting variable.
        List[str]: trans variable.
    """
    lines = list(map(str.strip, lines))

    check_lines(lines)

    for i in range(5):
        lines[i] = lines[i][lines[i].find('[') + 1: -1]

    states: List[str] = lines[0].split(',') if lines[0] else []
    alpha: List[str] = lines[1].split(',') if lines[1] else []
    initial: List[str] = lines[2].split(',') if lines[2] else []
    accepting: List[str] = lines[3].split(',') if lines[3] else []
    trans: List[str] = lines[4].split(',') if lines[4] else []

    for el in states:
        assert isalnum(el), "Only alphanumerical allowed!"
    for el in alpha:
        assert isalnum(el.replace('_', '')),\
            "Only alphanumerical and underscore allowed!"

    assert states != [], "States set should be non-empty!"
    assert alpha != [], "Alphabet set should be non-empty!"
    assert len(initial) <= 1, "Several initial states are not allowed!"

    return states, alpha, initial, accepting, trans


class FSA:
    def __init__(
        self,
        states: List[str],
        alpha: List[str],
        initial: List[str],
        accepting: List[str],
        trans: List[str],
    ):
        """Class for FSA

        Args:
            states (List[str]): states variable.
            alpha (List[str]): alpha variable.
            initial (List[str]): initial variable.
            accepting (List[str]): accepting variable.
            trans (List[str]): trans variable.
        """
        self.__states = states
        self.__alpha = alpha
        self.__initial = initial
        self.__accepting = accepting
        self.__trans = trans

        self.__n = len(self.__states)

        self.__state2id: Dict[str, int] = {
            self.__states[i]: i for i in range(self.__n)}
        self.__id2state: Dict[int, str] = {
            i: self.__states[i] for i in range(self.__n)}

        self.__graph: List[List[List[str]]] = [
            [[] for _ in range(self.__n)] for _ in range(self.__n)]
        self.__undirected_graph: List[List[List[str]]] = [
            [[] for _ in range(self.__n)] for _ in range(self.__n)]

        self.__create_graphs()

    def __create_graphs(self) -> None:
        """Create the directed and undirected graphs from transitions.
        """
        for el in self.__trans:
            s1, a, s2 = el.split('>')

            self.__graph[self.__state2id[s1]][self.__state2id[s2]].append(a)

            self.__undirected_graph[self.__state2id[s1]
                                    ][self.__state2id[s2]].append(a)
            self.__undirected_graph[self.__state2id[s2]
                                    ][self.__state2id[s1]].append(a)

    def Kleene(self) -> str:
        """Kleene's algorithm implementation.

        Returns:
            str: translated DFSA to RegExp.
        """
        # Check if FSA is correct
        if validation := self.validate():
            return validation
        R: List[List[str]] = [
            ['' for _ in range(self.__n)] for _ in range(self.__n)]

        # Initial sets
        for i in range(len(R)):
            for j in range(len(R)):
                if self.__graph[i][j]:
                    R[i][j] = '|'.join(sorted(self.__graph[i][j]))
                    R[i][j] += "|eps" if i == j else ''
                else:
                    R[i][j] = "eps" if i == j else "{}"
        R_prev: List[List[str]] = deepcopy(R)

        # Update the sets
        for k in range(len(R)):
            for i in range(len(R)):
                for j in range(len(R)):
                    R[i][j] = f"({R_prev[i][k]})({R_prev[k][k]})*({R_prev[k][j]})|({R_prev[i][j]})"
            R_prev = deepcopy(R)

        # Consider several accepting states case
        regs: List[str] = [R[self.__state2id[self.__initial[0]]][self.__state2id[f]]
                           for f in self.__accepting]
        result: str = '|'.join(map(lambda x: f"({x})", regs))
        return result

    def validate(self) -> str:
        """Validate FSA

        Returns:
            str: error.
        """
        if self.__check_E2():
            return "E2: Initial state is not defined"
        if self.__check_E3():
            return "E3: Set of accepting states is empty"
        if faulty_state := self.__check_E4():
            return f"E4: A state '{faulty_state}' is not in the set of states"
        if faulty_alpha := self.__check_E5():
            return f"E5: A transition '{faulty_alpha}' is not represented in the alphabet"
        if self.__check_E6():
            return "E6: Some states are disjoint"
        if self.__check_E7():
            return "E7: FSA is nondeterministic"
        return ""

    def __DFS(self, g: List[List[List[str]]], u: str, visited: Set[str]) -> Set[str]:
        """Depth-first search.

        Args:
            g: Graph.
            u (str): Node to start with.
            visited (set): Set of visited elements.
            undirected (bool): Whether to use the undirected graph.

        Returns:
            set: Set of visited elements.
        """
        visited.add(u)
        for v in range(self.__n):
            if self.__id2state[v] not in visited and g[self.__state2id[u]][v]:
                visited = self.__DFS(g, self.__id2state[v], visited)
        return visited

    def __check_E2(self) -> bool:
        """Function to check for error 2: \
            E2: Initial state is not defined.

        Returns:
            bool: Whether initial state is not defined.
        """
        return len(self.__initial) == 0

    def __check_E3(self) -> bool:
        """Function to check for error 3: \
            E3: Set of accepting states is empty.

        Returns:
            bool: Whether accepting state is not defined.
        """
        return len(self.__accepting) == 0

    def __check_E4(self) -> str:
        """Function to check for error 4: \
            E4: A state 's' is not in the set of states

        Returns:
            str: Faulty state or empty string.
        """
        for el in self.__initial:
            if el not in self.__states:
                return el
        for el in self.__accepting:
            if el not in self.__states:
                return el
        for el in self.__trans:
            s1, _, s2 = el.split('>')
            if s1 not in self.__states:
                return s1
            if s2 not in self.__states:
                return s2
        return ""

    def __check_E5(self) -> str:
        """Function to check for error 5: \
            E5: A transition 'a' is not represented in the alphabet

        Returns:
            str: Faulty alpha or empty string.
        """
        for el in self.__trans:
            _, a, _ = el.split('>')
            if a not in self.__alpha:
                return a
        return ""

    def __check_E6(self) -> bool:
        """Function to check for error 6: \
            E6: Some states are disjoint

        Returns:
            bool: Whether some states are disjoint.
        """
        visited = self.__DFS(self.__undirected_graph, self.__initial[0], set())
        return len(visited) != len(self.__states)

    def __check_E7(self) -> bool:
        """Function to check for error 7: \
            E7: FSA is nondeterministic.

        Returns:
            bool: Whether FSA is nondeterministic.
        """
        for u in range(self.__n):
            lst = []
            for v in range(self.__n):
                lst += self.__graph[u][v]
            for el in self.__alpha:
                if lst.count(el) > 1:
                    return True
        return False


def main() -> None:
    inp = open("input.txt", 'r')

    try:
        fsa = FSA(*parse_lines(inp.readlines()))
        result = fsa.Kleene()
        print(result)
    except AssertionError:
        print("E1: Input file is malformed")
    finally:
        inp.close()


if __name__ == "__main__":
    main()
