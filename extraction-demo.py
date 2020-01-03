import numpy as np

def geometric_mechanism(a, b):
    x = a + np.random.geometric(1 - b)
    y = a + np.random.geometric(1 - b)
    return x - y

def loop_geometric(inputs):
  loop_acc = (inputs, [])
  loop_cond = not [] == loop_acc[0]
  while loop_cond:
    if loop_acc[0]:
      uncons_head = loop_acc[0][0]
      uncons_tail = (loop_acc[0])[1:]
      uncons_result = (uncons_head, uncons_tail)
    else:
      uncons_result = None
    if loop_acc[0]:
      uncons_head1 = loop_acc[0][0]
      uncons_tail1 = (loop_acc[0])[1:]
      uncons_result1 = (uncons_head1, uncons_tail1)
    else:
      uncons_result1 = None
    if loop_acc[0]:
      uncons_head2 = loop_acc[0][0]
      uncons_tail2 = (loop_acc[0])[1:]
      uncons_result2 = (uncons_head2, uncons_tail2)
    else:
      uncons_result2 = None
    x = (geometric_mechanism(uncons_result[0][0], (np.exp((0.0 - uncons_result1[0][1][1]) / uncons_result2[0][1][0]))))
    if loop_acc[0]:
      uncons_head3 = loop_acc[0][0]
      uncons_tail3 = (loop_acc[0])[1:]
      uncons_result3 = (uncons_head3, uncons_tail3)
    else:
      uncons_result3 = None
    loop_acc = (uncons_result3[1], loop_acc[1] + [x])
    loop_cond = not [] == loop_acc[0]
  x1 = loop_acc
  return x1[1]

print(loop_geometric([[1, [2, 3]],
                      [2, [2, 3]],
                     ]))
