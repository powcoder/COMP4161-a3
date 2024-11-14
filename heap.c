https://powcoder.com
代写代考加微信 powcoder
Assignment Project Exam Help
Add WeChat powcoder



struct tree_heap {
  unsigned int delay;
  void *data;
  struct tree_heap *left;
  struct tree_heap *right;
};

#define NULL ((void *) 0)


/* Replace the top values of the heap. */
void
set_top (struct tree_heap* p, unsigned int delay, void *data) {
  p->delay = delay;
  p->data = data;
}

struct tree_heap *
min_delay (struct tree_heap* p, int delay,
        struct tree_heap *p2, struct tree_heap *p3) {

  if (p2 && (p2->delay < delay)) {
    delay = p2->delay;
    p = p2;
  }
  if (p3 && (p3->delay < delay)) {
    p = p3;
  }
  return p;
}

/* Replace the top values of the heap and, if the new entry is not of the
    highest priority, push it down to maintain the sorted order. */
void
push_down (struct tree_heap* heap, int delay, void *data) {
  struct tree_heap* min;

  while (heap) {

    min = min_delay(heap, delay, heap->left, heap->right);

    if (min == heap->left) {
      /* copy current values at heap->left up to top */
      set_top(heap, heap->left->delay, heap->left->data);
      /* keep pushing the current value down into the left tree */
      heap = heap->left;
    }
    else if (min == heap->right) {
      /* copy current values at heap->right up to top */
      set_top(heap, heap->right->delay, heap->right->data);
      /* keep pushing the current value down into the right tree */
      heap = heap->right;
    }
    else {
      /* place current values at this site */
      set_top(heap, delay, data);
      /* terminate the loop */
      heap = NULL;
    }
  }
}


