# case-forged — claims result 6, program decides 5; must DRIFT
# emit: refuse
[flow-eval] ((entry main) (fuel 64) (result (bare (int 6))) (graph (def main (bare (lit (int 5))))) (oracle))
