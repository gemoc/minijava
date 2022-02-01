package org.tetrabox.minijava.semantics

import fr.inria.diverse.k3.al.annotationprocessor.Aspect

import fr.inria.diverse.k3.al.annotationprocessor.OverrideAspectMethod
import java.util.HashMap
import java.util.Map
import org.tetrabox.minijava.model.miniJava.ArrayRefValue
import org.tetrabox.minijava.model.miniJava.BooleanValue
import org.tetrabox.minijava.model.miniJava.Call
import org.tetrabox.minijava.model.miniJava.Context
import org.tetrabox.minijava.model.miniJava.Frame
import org.tetrabox.minijava.model.miniJava.IntegerValue
import org.tetrabox.minijava.model.miniJava.MiniJavaFactory
import org.tetrabox.minijava.model.miniJava.NullValue
import org.tetrabox.minijava.model.miniJava.ObjectInstance
import org.tetrabox.minijava.model.miniJava.ObjectRefValue
import org.tetrabox.minijava.model.miniJava.State
import org.tetrabox.minijava.model.miniJava.StringValue
import org.tetrabox.minijava.model.miniJava.SymbolBinding
import org.tetrabox.minijava.model.miniJava.Value
import org.tetrabox.minijava.model.miniJava.Symbol
import static extension org.tetrabox.minijava.semantics.ContextAspect.*
import static extension org.tetrabox.minijava.semantics.FrameAspect.*

@Aspect(className=Context)
class ContextAspect {

	private val Map<Symbol, SymbolBinding> cache = new HashMap

	def Context createChildContext() {
		return MiniJavaFactory::eINSTANCE.createContext => [
			parentContext = _self
		]
	}

	def SymbolBinding findBinding(Symbol symbol) {
		if (!_self.cache.containsKey(symbol)) {
			val binding = _self.bindings.findFirst[it.symbol === symbol]
			if (binding !== null) {
				_self.cache.put(symbol, binding)
			} else if (_self.parentContext !== null) {
				val binding2 = _self.parentContext.findBinding(symbol)
				_self.cache.put(symbol, binding2)
			} else {
				throw new Exception("No binding for symbol " + symbol)
			}
		}
		return _self.cache.get(symbol)
	}

	def Context findCurrentContext() {
		if (_self.childContext !== null) {
			return _self.childContext.findCurrentContext
		} else {
			return _self
		}
	}

}

@Aspect(className=State)
class StateAspect {

	private var Frame frameCache
	private var Context contextCache

	def Frame findCurrentFrame() {
		if (_self.frameCache === null) {
			_self.frameCache = _self.rootFrame.findCurrentFrame
		}
		return _self.frameCache
	}

	def Context findCurrentContext() {
		if (_self.contextCache === null) {
			_self.contextCache = _self.rootFrame.findCurrentContext
		}
		return _self.contextCache
	}

	def void println(String string) {
		println(string)
		_self.outputStream.stream.add(string)
	}

	def void pushNewContext() {
		val newContext = MiniJavaFactory::eINSTANCE.createContext
		if (_self.findCurrentContext !== null) {
			_self.findCurrentContext.childContext = newContext
		} else {
			_self.findCurrentFrame.rootContext = newContext
		}
		_self.contextCache = newContext
	}

	def void popCurrentContext() {
		val newCurrent = _self.findCurrentContext.parentContext
		_self.findCurrentContext.parentContext = null
		_self.contextCache = newCurrent
	}

	def void pushNewFrame(ObjectInstance receiver, Call c, Context newContext) {
		val newFrame = MiniJavaFactory::eINSTANCE.createFrame => [
			instance = receiver
			call = c
			rootContext = newContext
		]
		_self.findCurrentFrame.childFrame = newFrame
		_self.frameCache = newFrame
		_self.contextCache = null

	}

	def void popCurrentFrame() {
		val newCurrent = _self.findCurrentFrame.parentFrame
		_self.findCurrentFrame.parentFrame = null;
		_self.contextCache = null
		_self.frameCache = newCurrent
	}

}

@Aspect(className=Frame)
class FrameAspect {

	def Frame findCurrentFrame() {
		if (_self.childFrame !== null) {
			return _self.childFrame.findCurrentFrame
		} else {
			return _self
		}
	}

	def Context findCurrentContext() {
		if (_self.childFrame !== null) {
			return _self.childFrame.findCurrentContext
		} else if (_self.rootContext !== null) {
			return _self.rootContext.findCurrentContext
		} else {
			return null
		}
	}

}

@Aspect(className=Value)
class ValueAspect {
	def Value copy() { throw new Exception("Must provide a copy method for " + _self) }
}

@Aspect(className=IntegerValue)
class IntegerValueAspect extends ValueAspect {
	@OverrideAspectMethod
	def Value copy() {
		return MiniJavaFactory::eINSTANCE.createIntegerValue => [value = _self.value]
	}
}

@Aspect(className=BooleanValue)
class BooleanValueAspect extends ValueAspect {
	@OverrideAspectMethod
	def Value copy() {
		return MiniJavaFactory::eINSTANCE.createBooleanValue => [value = _self.value]
	}
}

@Aspect(className=StringValue)
class StringValueAspect extends ValueAspect {
	@OverrideAspectMethod
	def Value copy() {
		return MiniJavaFactory::eINSTANCE.createStringValue => [value = _self.value]
	}

}

@Aspect(className=ObjectRefValue)
class ObjectRefValueAspect extends ValueAspect {
	@OverrideAspectMethod
	def Value copy() {
		return MiniJavaFactory::eINSTANCE.createObjectRefValue => [instance = _self.instance]
	}
}

@Aspect(className=ArrayRefValue)
class ArrayRefValueAspect extends ValueAspect {
	@OverrideAspectMethod
	def Value copy() {
		return MiniJavaFactory::eINSTANCE.createArrayRefValue => [instance = _self.instance]
	}
}

@Aspect(className=NullValue)
class NullValueAspect extends ValueAspect {
	@OverrideAspectMethod
	def Value copy() {
		return MiniJavaFactory::eINSTANCE.createNullValue
	}
}
