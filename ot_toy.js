'use strict';
// Copyright 2016 Google Inc. All rights reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// A testbed for operational transformation ideas.


function xi(tree, i) {
  var base = 0;
  while (tree != null) {
    var left = tree.left;
    var x = tree.value - ((left && left.size) || 0);
    if (i < x) {
      tree = left;
    } else {
      i = 1 + i - x;
      base += tree.value;
      tree = tree.right;
    }
  }
  return base + i;
}

// precondition: i is not a member of the set
function xiInv(tree, i) {
  var result = i;
  var x = 0;
  while (tree != null) {
    if (i < tree.value) {
      tree = tree.left;
    } else {
      i -= tree.value;
      result++;
      if (tree.left && tree.left.size) {
        result -= tree.left.size;
      }
      tree = tree.right;
    }
  }
  return result;
}

function contains(tree, i) {
  while (tree != null) {
    if (i < tree.value) {
      tree = tree.left;
    } else if (i == tree.value) {
      return true;
    } else { // i > tree.value
      i -= tree.value;
      tree = tree.right;
    }
  }
  return false;
}

function mkTreeRaw(left, value, right) {
  var size = 1 + ((left && left.size) || 0) + ((right && right.size) || 0);
  var leftHeight = left == null ? 0 : left.height;
  var rightHeight = right == null ? 0 : right.height;
  var height = Math.max(leftHeight, rightHeight) + 1;
  return {
    left: left,
    value: value,
    right: right,
    size: size,
    height: height
  };
}

function mkTree(left, value, right) {
  var leftHeight = left == null ? 0 : left.height;
  var rightHeight = right == null ? 0 : right.height;
  if (leftHeight > rightHeight + 1) {
    // unbalanced, rotate right
    return mkTreeRaw(left.left, left.value, mkTreeRaw(left.right, value - left.value, right));
  } else if (rightHeight > leftHeight + 1) {
    // unbalanced, rotate left
    return mkTreeRaw(mkTreeRaw(left, value, right.left), value + right.value, right.right);
  }
  return mkTreeRaw(left, value, right);
}

function unionOne(tree, i) {
  if (tree == null) {
    return mkTree(null, i, null);
  } else if (i < tree.value) {
    return mkTree(unionOne(tree.left, i), tree.value, tree.right);
  } else if (i == tree.value) {
    return tree;
  } else {  // i > tree.value
    return mkTree(tree.left, tree.value, unionOne(tree.right, i - tree.value));
  }
}

// \Xi_{i}(S)
function xiOne(tree, i) {
  if (tree == null) {
    return null;
  } else if (i <= tree.value) {
    return mkTree(xiOne(tree.left, i), tree.value + 1, tree.right);
  } else {
    return mkTree(tree.left, tree.value, xiOne(tree.right, i - tree.value));
  }
}

// transformations of operations
// All operations have 'ty' and 'ix' properties
// also 'id'
// sample operations:
// {ty: 'ins', ix: 1, ch: 'x', pri: 0}
// {ty: 'del', ix: 1}

// Note: mutating in place is appealing, to avoid allocations.
function transform(op1, op2) {
  if (op2.ty != 'ins') { return op1; }
  return transformIns(op1, op2.ix, op2.pri);
}

function transformIns(op1, ix, pri) {
  if (op1.ty == 'ins') {
    if (op1.ix < ix || (op1.ix == ix && op1.pri < pri)) {
      return op1;
    }
    return {
      ty: op1.ty,
      ix: op1.ix + 1,
      ch: op1.ch,
      pri: op1.pri,
      id: op1.id
    };
  } else { // op1.ty is del
    if (op1.ix < ix) {
      return op1;
    }
    return {
      ty: op1.ty,
      ix: op1.ix + 1,
      id: op1.id
    };
  }
}

class DocState {
  constructor() {
    this.ops = [];
    this.dels = null;
    this.str = '';
    this.points = [];  // in user-visible string coordinates
  }

  add(op) {
    this.ops.push(op);
    if (op.ty == 'del') {
      if (!contains(this.dels, op.ix)) {
        var ix = xiInv(this.dels, op.ix);
        this.dels = unionOne(this.dels, op.ix);
        this.str = this.str.slice(0, ix) + this.str.slice(ix + 1);
        for (var i = 0; i < this.points.length; i++) {
          if (this.points[i] > ix) {
            this.points[i] -= 1;
          }
        }
      }
    } else if (op.ty == 'ins') {
      this.dels = xiOne(this.dels, op.ix);
      var ix = xiInv(this.dels, op.ix);
      this.str = this.str.slice(0, ix) + op.ch + this.str.slice(ix);
      for (var i = 0; i < this.points.length; i++) {
        if (this.points[i] > ix) {
          this.points[i] += 1;
        }
      }
    }
  }

  xFormIx(ix) {
    return xi(this.dels, ix);
  }

  getStr() {
    return this.str;
  }
}

class Peer {
  constructor() {
    this.rev = 0;
    this.context = new Set();
  }

  mergeOp(docState, op) {
    var id = op.id;
    var ops = docState.ops;
    if (this.rev < ops.length && ops[this.rev].id == id) {
      // we already have this, roll rev forward
      this.rev++;
      while (this.rev < ops.length && this.context.has(ops[this.rev].id)) {
        this.context.delete(ops[this.rev].id);
        this.rev++;
      }
      return;
    }
    for (var ix = this.rev; ix < ops.length; ix++) {
      if (ops[ix].id == id) {
        // we already have this, but can't roll rev forward
        this.context.add(id);
        return;
      }
    }
    // we don't have it, need to merge
    var insList = [];
    var S = null;
    var T = null;
    for (var ix = ops.length - 1; ix >= this.rev; ix--) {
      var myOp = ops[ix];
      if (myOp.ty == 'ins') {
        var i = xi(S, myOp.ix);
        if (!this.context.has(myOp.id)) {
          insList.push([xiInv(T, i), myOp.pri]);
          T = unionOne(T, i);
        }
        S = unionOne(S, i);
      }
    }
    for (var i = insList.length - 1; i >= 0; i--) {
      op = transformIns(op, insList[i][0], insList[i][1]);
    }
    var current = (this.rev == ops.length);
    docState.add(op);
    if (current) {
      this.rev++;
    } else {
      this.context.add(id);
    }
  }
}

// Export as a module for node, but don't bother namespacing for browser
if (typeof exports !== 'undefined') {
  exports.DocState = DocState;
  exports.Peer = Peer;
}
