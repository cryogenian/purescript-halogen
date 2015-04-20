-- | This module provides the FFI definitions required to render HTML documents
-- | using the `virtual-dom` library.

module Halogen.Internal.VirtualDOM
  ( VTree()
  , Patch()
  , Props()
  , Widget()
  , emptyProps
  , prop
  , handlerProp
  , initProp
  , finalizerProp
  , createElement
  , diff
  , patch
  , vtext
  , vnode
  , vwidget
  , widget
  ) where

import DOM
import Data.DOM.Simple.Types

import Data.Maybe
import Data.Monoid
import Data.Nullable
import Data.Function

import Control.Monad.Eff
import Control.Monad.ST

-- | Virtual DOM nodes
data VTree

-- | Patch sets, used to update the DOM
data Patch

-- | Property collections
data Props

-- | A third-party widget
data Widget (eff :: # !) i

foreign import emptyProps 
  "var emptyProps = {}" :: Props

-- | Create a property from a key/value pair.
-- | 
-- | Properties named `data-*` will be added as attributes, and any other properties will
-- | be set directly.
-- |
-- | Users should use caution when creating custom attributes, and understand how they will
-- | be added to the DOM here.
foreign import prop
  """function prop(key, value) {
    var props = {attributes: {}},
        toAttr = function(key) {
          if (key == 'readonly') return true;
          if (key.indexOf('data-') == 0) return true;
        };
    
    if (toAttr(key)) {
      props.attributes[key] = value;
    } else {
      props[key] = value;
    }
    return props;
  }""" :: forall value. Fn2 String value Props


-- | Create a property from an event handler
foreign import handlerProp
  "function handlerProp(key, f) {\
  \  var props = {};\
  \  var Hook = function () {};\
  \  Hook.prototype.callback = function(e) {\
  \    f(e)();\
  \  };\
  \  Hook.prototype.hook = function(node) {\
  \    node.addEventListener(key, this.callback);\
  \  };\
  \  Hook.prototype.unhook = function(node) {\
  \    node.removeEventListener(key, this.callback);\
  \  };\
  \  props['halogen-hook-' + key] = new Hook(f);\
  \  return props;\
  \}" :: forall eff event. Fn2 String (event -> Eff eff Unit) Props

-- | Create a property from an initializer
foreign import initProp
  "function initProp(f) {\
  \  var props = {};\
  \  var Hook = function () {};\
  \  Hook.prototype.hook = function(node, prop, prev) {\
  \    if (typeof prev === 'undefined') {\
  \      f();\
  \    };\
  \  };\
  \  props['halogen-init'] = new Hook(f);\
  \  return props;\
  \}" :: forall eff. Eff eff Unit -> Props
  
-- | Create a property from an finalizer
foreign import finalizerProp
  "function finalizerProp(f) {\
  \  var props = {};\
  \  var Hook = function () {};\
  \  Hook.prototype.hook = function() { };\
  \  Hook.prototype.unhook = function() {\
  \    f();\
  \  };\
  \  props['halogen-finalizer'] = new Hook(f);\
  \  return props;\
  \}" :: forall eff. Eff eff Unit -> Props


foreign import concatProps
  """function concatProps(p1, p2) {
    var props = {},
        a1 = p1.attributes || {},
        a2 = p1.attributes || {},
        a = {},
        key;
    var flag = false;
    for (var key in a2) {
      if (a2.hasOwnProperty(key)) {
        a[key] = a2[key];
      }
    }
    for (var key in a1) {
      if (a1.hasOwnProperty(key)) {
        a[key] = a1[key];
      }
    }
    delete p1.attributes;
    delete p2.attributes;
    for (var key in p1) {
      if (p1.hasOwnProperty(key)) {
        props[key] = p1[key];
      }
    }
    for (var key in p2) {
      if (p2.hasOwnProperty(key)) {
        props[key] = p2[key];
      }
    }
    props.attributes = a;
    if (flag) console.log(props);
    return props;
  }""" :: Fn2 Props Props Props

instance semigroupProps :: Semigroup Props where
  (<>) = runFn2 concatProps
  
instance monoidProps :: Monoid Props where
  mempty = emptyProps

-- | Create a DOM node from a virtual DOM tree
foreign import createElement
  "function createElement(vtree) {\
  \  return require('virtual-dom/create-element')(vtree);\
  \}" :: VTree -> HTMLElement

-- | Calculate the differences between two virtual DOM trees
foreign import diff
  "function diff(vtree1) {\
  \  return function createElement(vtree2) {\
  \    return require('virtual-dom/diff')(vtree1, vtree2);\
  \  };\
  \}" :: VTree -> VTree -> Patch
  
-- | Apply a set of patches to the DOM
foreign import patch
  "function patch(p) {\
  \  return function(node) {\
  \    return function() {\
  \      return require('virtual-dom/patch')(node, p);\
  \    };\
  \  };\
  \}" :: forall eff. Patch -> HTMLElement -> Eff (dom :: DOM | eff) HTMLElement

-- | Create a virtual DOM tree which represents a single text node
foreign import vtext 
  "function vtext(s) {\
  \  var VText = require('virtual-dom/vnode/vtext');\
  \  return new VText(s);\
  \}" :: String -> VTree

-- | Create a virtual DOM tree which represents an element with properties
foreign import vnode 
  "function vnode(name) {\
  \  return function(attr) {\
  \    return function(children) {\
  \      var VirtualNode = require('virtual-dom/vnode/vnode');\
  \      var props = {\
  \        attributes: {}\
  \      };\
  \      for (var key in attr) {\
  \        if (key.indexOf('data-') === 0) {\
  \          props.attributes[key] = attr[key];\
  \        } else {\
  \          props[key] = attr[key];\
  \        }\
  \      }\
  \      return new VirtualNode(name, props, children);\
  \    };\
  \  };\
  \}" :: String -> Props -> [VTree] -> VTree

-- | Create a virtual DOM tree from a `Widget`
foreign import vwidget 
  "function vwidget(driver) {\
  \  return function(w) {\
  \    return w.create(driver);\
  \  };\
  \}" :: forall eff i. (i -> Eff eff Unit) -> Widget eff i -> VTree
  
foreign import mapWidget 
  "function mapWidget(f) {\
  \  return function(w) {\
  \    return {\
  \      create: function(driver) {\
  \        return w.create(function(i) {\
  \          return driver(f(i));\
  \        });\
  \      }\
  \    };\
  \  };\
  \}" :: forall eff i j. (i -> j) -> Widget eff i -> Widget eff j
  
instance functorWidget :: Functor (Widget eff) where
  (<$>) = mapWidget
  
foreign import widget
  "function widget(name, id, init, update, destroy) {\
  \  return {\
  \    create: function(driver) {\
  \      var Widget = function () {};\
  \      Widget.prototype.type = 'Widget';\
  \      Widget.prototype.name = name;\
  \      Widget.prototype.id = id;\
  \      Widget.prototype.init = function(){\
  \        var state = init(driver)();\
  \        this.state = state.state;\
  \        return state.node;\
  \      };\
  \      Widget.prototype.update = function(prev, node) {\
  \        var updated = update(prev.state)(node)();\
  \        this.state = prev.state;\
  \        return updated;\
  \      };\
  \      Widget.prototype.destroy = function(node) {\
  \        destroy(this.state)(node)();\
  \      };\
  \      return new Widget();\
  \    }\
  \  };\
  \}" :: forall eff i s. Fn5 String
                             String
                             ((i -> Eff eff Unit) -> Eff eff { state :: s, node :: HTMLElement })
                             (s -> HTMLElement -> Eff eff (Nullable HTMLElement))
                             (s -> HTMLElement -> Eff eff Unit)
                             (Widget eff i)
