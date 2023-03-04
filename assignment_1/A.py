# Dmitriy Okoneshnikov
from typing import List, Tuple, Dict


def check_lines(lines: List[str]) -> None:
    """Check if the necessary variables are in input.

    Args:
        lines (List[str]): List containing a variable on each line.
    """
    assert len(lines) == 5,\
        'Input file should contain 5 variables: states, alpha, init.st, fin.st, and trans!'
    assert lines[0].startswith('states=['),\
        'Input file should contain variable `states`!'
    assert lines[1].startswith('alpha=['),\
        'Input file should contain variable `alpha`!'
    assert lines[2].startswith('init.st=['),\
        'Input file should contain variable `init.st`!'
    assert lines[3].startswith('fin.st=['),\
        'Input file should contain variable `fin.st`!'
    assert lines[4].startswith('trans=['),\
        'Input file should contain variable `trans`!'


def parse_lines(lines: List[str]) ->\
        Tuple[List[str], List[str], List[str], List[str], List[str]]:
    """Parse lines of input.

    Returns:
        List[str]: states variable.
        List[str]: alpha variable.
        List[str]: init.st variable.
        List[str]: fin.st variable.
        List[str]: trans variable.
    """
    lines = list(map(str.strip, lines))
    lines = list(filter(lambda x: len(x) > 0, lines))

    check_lines(lines)

    for i in range(5):
        lines[i] = lines[i][lines[i].find('[') + 1: -1]

    states: List[str] = lines[0].split(',') if lines[0] else []
    alpha: List[str] = lines[1].split(',') if lines[1] else []
    init_st: List[str] = lines[2].split(',') if lines[2] else []
    fin_st: List[str] = lines[3].split(',') if lines[3] else []
    trans: List[str] = lines[4].split(',') if lines[4] else []

    for el in states:
        assert el.isalnum(), "Only alphanumerical allowed!"
    for el in alpha:
        assert el.replace('_', '').isalnum(),\
            "Only alphanumerical and underscore allowed!"

    assert states != [], "States set should be non-empty!"
    assert alpha != [], "Alphabet set should be non-empty!"

    return states, alpha, init_st, fin_st, trans


class FSA_validator:
    def __init__(
        self,
        states: List[str],
        alpha: List[str],
        init_st: List[str],
        fin_st: List[str],
        trans: List[str],
    ):
        """Class for validating FSA

        Args:
            states (List[str]): states variable.
            alpha (List[str]): alpha variable.
            init_st (List[str]): init.st variable.
            fin_st (List[str]): fin.st variable.
            trans (List[str]): trans variable.
        """
        self.__states = states
        self.__alpha = alpha
        self.__init_st = init_st
        self.__fin_st = fin_st
        self.__trans = trans
        self.__graph: Dict[str, List[Tuple[str, str]]] = {}
        self.__undirected_graph: Dict[str, List[Tuple[str, str]]] = {}

    def create_graphs(self) -> None:
        """Create the directed and undirected graphs from transitions.
        """
        for el in self.__trans:
            s1, a, s2 = el.split('>')

            if s1 not in self.__states or s2 not in self.__states:
                continue

            if s1 not in self.__graph:
                self.__graph[s1] = []
            self.__graph[s1].append((s2, a))

            if s1 not in self.__undirected_graph:
                self.__undirected_graph[s1] = []
            self.__undirected_graph[s1].append((s2, a))
            if s2 not in self.__undirected_graph:
                self.__undirected_graph[s2] = []
            self.__undirected_graph[s2].append((s1, a))

        for el in self.__states:
            if el not in self.__graph:
                self.__graph[el] = []
            if el not in self.__undirected_graph:
                self.__undirected_graph[el] = []

    def validate(self) -> Tuple[str, str, List[str]]:
        """Validate FSA

        Returns:
            str: errors.
            str: FSA complete/incomplete.
            List[str]: warnings.
        """
        if faulty_state := self.check_E1():
            return f"E1: A state '{faulty_state}' is not in the set of states", "", []
        self.create_graphs()
        if self.check_E2():
            return "E2: Some states are disjoint", "", []
        if faulty_alpha := self.check_E3():
            return f"E3: A transition '{faulty_alpha}' is not represented in the alphabet", "", []
        if self.check_E4():
            return "E4: Initial state is not defined", "", []

        warnings: List[str] = []
        if self.check_W1():
            warnings.append("W1: Accepting state is not defined")
        if self.check_W2():
            warnings.append(
                "W2: Some states are not reachable from the initial state"
            )
        if self.check_W3():
            warnings.append("W3: FSA is nondeterministic")

        completion = ""
        for u in self.__graph:
            if len(set([x[1] for x in self.__graph[u]])) < len(self.__alpha):
                completion = "FSA is incomplete"
                break
        else:
            completion = "FSA is complete"

        return "", completion, warnings

    def check_E1(self) -> str:
        """Function to check for error 1: \
            E1: A state 's' is not in the set of states.

        Returns:
            str: Faulty state or empty string.
        """
        for el in self.__init_st:
            if el not in self.__states:
                return el
        for el in self.__fin_st:
            if el not in self.__states:
                return el
        # for el in self.__trans:
        #     s1, _, s2 = el.split('>')
            # if s1 not in self.__states:
            #     return s1
            # if s2 not in self.__states:
            #     return s2
        return ""

    def DFS(self, u: str, visited: set, undirected: bool) -> set:
        """Depth-first search.

        Args:
            u (str): Node to start with.
            visited (set): Set of visited elements.
            undirected (bool): Whether to use the undirected graph.

        Returns:
            set: Set of visited elements.
        """
        visited.add(u)
        for v in (self.__undirected_graph[u] if undirected else self.__graph[u]):
            if v[0] not in visited:
                visited = self.DFS(v[0], visited, undirected)
        return visited

    def check_E2(self) -> bool:
        """Function to check for error 2: \
            E2: Some states are disjoint.

        Returns:
            bool: Whether some states are disjoint.
        """
        visited = self.DFS(self.__states[0], set(), True)
        return len(visited) != len(self.__states)

    def check_E3(self) -> str:
        """Function to check for error 3: \
            E3: A transition 'a' is not represented in the alphabet.

        Returns:
            str: Faulty alpha or empty string.
        """
        for el in self.__trans:
            _, a, _ = el.split('>')
            if a not in self.__alpha:
                return a
        return ""

    def check_E4(self) -> bool:
        """Function to check for error 4: \
            E4: Initial state is not defined.

        Returns:
            bool: Whether initial state is not defined.
        """
        return len(self.__init_st) == 0

    def check_W1(self) -> bool:
        """Function to check for warning 1: \
            W1: Accepting state is not defined.

        Returns:
            bool: Whether accepting state is not defined.
        """
        return len(self.__fin_st) == 0

    def check_W2(self) -> bool:
        """Function to check for warning 2: \
            W2: Some states are not reachable from the initial state.

        Returns:
            bool: Whether some states are not reachable from the initial state.
        """
        visited = self.DFS(self.__init_st[0], set(), False)
        return len(visited) != len(self.__states)

    def check_W3(self) -> bool:
        """Function to check for warning 3: \
            W3: FSA is nondeterministic.

        Returns:
            int: Whether FSA is nondeterministic.
        """
        for u in self.__graph:
            lst = list([x[1] for x in self.__graph[u]])
            for el in self.__alpha:
                if lst.count(el) > 1:
                    return True
        return False


def main() -> None:
    inp = open('fsa.txt', 'r')
    out = open('result.txt', 'w')

    states, alpha, init_st, fin_st, trans = [], [], [], [], []
    try:
        states, alpha, init_st, fin_st, trans = parse_lines(inp.readlines())
    except AssertionError:
        out.write("Error:\nE5: Input file is malformed\n")
    else:
        validator = FSA_validator(
            states, alpha, init_st, fin_st, trans
        )
        error, completion, warnings = validator.validate()
        if error:
            out.write(f"Error:\n{error}\n")
        else:
            out.write(f"{completion}\n")
            if warnings:
                out.write("Warning:\n")
                for warn in warnings:
                    out.write(f"{warn}\n")
    finally:
        inp.close()
        out.close()


if __name__ == "__main__":
    main()
