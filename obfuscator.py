#!/usr/bin/env python
# -*- coding: utf-8 -*-

import io
import os
import ast
import sys
import getopt
import shutil
import difflib
import keyword
import unparse

class Obfuscator(ast.NodeTransformer):
	__current__ = bytearray('a');

	def __init__(self, mapper):
		self._level = 0;
		self._attrs = [];
		self._names = mapper;
		self._mapper = {};
		self._classes = [];
		self._methods = [];
		self._pending = {};
		self._constants = [];
		self._attrsStack = [];
		self._methodStack = [];
		self._mapperStack = [];
		self._pendingStack = [];

	def _make(self):
		index = 0;
		result = str(Obfuscator.__current__);
		Obfuscator.__current__[0] += 1;
		while Obfuscator.__current__[index] > ord('z'):
			Obfuscator.__current__[index] = 'a';
			if index < len(Obfuscator.__current__) - 1:
				index += 1;
				Obfuscator.__current__[index] += 1;
			else:
				Obfuscator.__current__.extend(bytearray('a'));
				break;
		return result[::-1];

	def _rename(self, name):
		if name == 'self':
			return name;
		if name not in self._names:
			self._names[name] = self._make();
		if name not in self._mapper:
			self._mapper[name] = self._names[name]
			while keyword.iskeyword(self._names[name]):
				self._names[name] = self._make();
			if name in self._pending:
				for node, attr in self._pending[name]:
					setattr(node, attr, self._names[name]);
				del self._pending[name];
		return self._names[name];

	def _defered(self, node, attr):
		name = getattr(node, attr);
		if name not in self._pending:
			self._pending[name] = [];
		self._pending[name].append((node, attr));

	def _saveState(self):
		self._attrsStack.append(self._attrs[:]);
		self._methodStack.append(self._methods[:]);
		self._mapperStack.append(dict(self._mapper));
		self._pendingStack.append(dict(self._pending));
		self._methods = [];
		self._pending = {};

	def _restoreState(self):
		self._attrs = self._attrsStack.pop();
		self._mapper = self._mapperStack.pop();
		self._methods = self._methodStack.pop();
		self._pending.update(self._pendingStack.pop());

	def _renameAssignTuple(self, tp):
		for element in tp.elts:
			elementType = type(element);
			if elementType is ast.Name:
				if self._level == 0:
					self._constants.append((element.id, self._rename(element.id)));
			elif elementType is ast.Tuple:
				self._renameAssignTuple(element);
			elif elementType in (ast.Attribute, ast.Subscript):
				self._renameAssignTarget(element);

	def _renameAssignTarget(self, target):
		valueType = type(target.value);
		if valueType is ast.Name:
			if target.value.id == 'self':
				if target.attr.startswith('_'):
					self._attrs.append(target.attr);
					target.attr = self._rename(target.attr);
		elif valueType is ast.Subscript:
			self._renameAssignTarget(target.value);

	def _obfuscateStringLiteral(self, string):
		elements = [];
		for x in bytearray(string):
			elements.append(ast.Num(n = x));
		return ast.Call(
			func = ast.Name(id = 'str', ctx = ast.Load()),
			args = [ast.Call(
				func = ast.Name(id = 'bytearray', ctx = ast.Load()),
				args = [ast.List(elts = elements, ctx = ast.Load())],
				kwargs = None,
				keywords = [],
				starargs = None
			)],
			kwargs = None,
			keywords = [],
			starargs = None
		);

	def _obfuscateUnicodeLiteral(self, string):
		return ast.Call(
			args = [ast.Str(s = 'utf-8')],
			func = ast.Attribute(
				ctx = ast.Load(),
				attr = 'decode',
				value = self._obfuscateStringLiteral(string.encode('utf-8'))
			),
			kwargs = None,
			keywords = [],
			starargs = None
		);

	def visit_If(self, node):
		self._level += 1;
		self.generic_visit(node);
		self._level -= 1;
		return node;

	def visit_For(self, node):
		self._level += 1;
		self.generic_visit(node);
		self._level -= 1;
		return node;

	def visit_Str(self, node):
		sType = type(node.s);
		if sType is str:
			return self._obfuscateStringLiteral(node.s);
		elif sType is unicode:
			return self._obfuscateUnicodeLiteral(node.s);
		else:
			return node;

	def visit_Name(self, node):
		if not node.id.startswith('__'):
			if node.id not in __builtins__.__dict__:
				node.id = self._rename(node.id);
		return node;

	def visit_With(self, node):
		self._level += 1;
		self.generic_visit(node);
		self._level -= 1;
		return node;

	def visit_While(self, node):
		self._level += 1;
		self.generic_visit(node);
		self._level -= 1;
		return node;

	def visit_Global(self, node):
		node.names = map(self._rename, node.names);
		return node;

	def visit_Assign(self, node):
		for target in node.targets:
			targetType = type(target);
			if targetType is ast.Name:
				if not target.id.startswith('_'):
					if self._level == 0:
						self._constants.append((target.id, self._rename(target.id)));
			elif targetType is ast.Tuple:
				self._renameAssignTuple(target);
			elif targetType in (ast.Attribute, ast.Subscript):
				self._renameAssignTarget(target);
		self.generic_visit(node);
		return node;

	def visit_Import(self, node):
		for name in node.names:
			name.asname = self._rename(name.name);
		map(self.generic_visit, node.names);
		return node;

	def visit_ClassDef(self, node):
		newName = self._rename(node.name);
		if not node.name.startswith('_'):
			self._classes.append((node.name, newName));
		remove = [];
		node.name = newName;
		self._saveState();
		for item in node.body:
			if type(item) is ast.Assign:
				discard = [];
				for target in item.targets:
					if type(target) is ast.Name:
						if target.id == '__slots__':
							discard.append(target);
				for target in discard:
					item.targets.remove(target);
				if item.targets == []:
					remove.append(item);
		for item in remove:
			node.body.remove(item);
		self._level += 1;
		self.generic_visit(node);
		self._level -= 1;
		for name, alias in self._methods:
			node.body.append(ast.Assign(targets = [ast.Name(id = name, ctx = ast.Store())], value = ast.Name(id = alias, ctx = ast.Store())));
		self._restoreState();
		return node;

	def visit_TryExcept(self, node):
		self._level += 1;
		self.generic_visit(node);
		self._level -= 1;
		return node;

	def visit_Attribute(self, node):
		if type(node.value) is ast.Name:
			if node.value.id == 'self':
				if node.attr not in self._attrs and node.attr not in self._mapper:
					self._defered(node, 'attr');
				else:
					node.attr = self._rename(node.attr);
		self.generic_visit(node);
		return node;

	def visit_TryFinally(self, node):
		self._level += 1;
		self.generic_visit(node);
		self._level -= 1;
		return node;

	def visit_ImportFrom(self, node):
		for name in node.names:
			name.asname = self._rename(name.name);
		map(self.generic_visit, node.names);
		return node;

	def visit_FunctionDef(self, node):
		if not node.name.startswith('__'):
			self._attrs.append(node.name);
			newName = self._rename(node.name);
			if not node.name.startswith('_'):
				self._methods.append((node.name, newName));
			node.name = newName;
		if node.args.kwarg is not None:
			node.args.kwarg = self._rename(node.args.kwarg);
		if node.args.vararg is not None:
			node.args.vararg = self._rename(node.args.vararg);
		self._level += 1;
		self.generic_visit(node);
		self._level -= 1;
		return node;

	def visit_ExceptHandler(self, node):
		self._level += 1;
		self.generic_visit(node);
		self._level -= 1;
		return node;

	def obfuscate(self, fp):
		node = self.visit(ast.parse(fp.read()));
		for name, alias in (self._constants + self._classes + self._methods):
			node.body.append(ast.Assign(targets = [ast.Name(id = name, ctx = ast.Store())], value = ast.Name(id = alias, ctx = ast.Store())));
		return node;

def usage():
	print 'usage: %s [-h|--help] [-r|--recursive] [-o|--overwrite] args ...' % sys.argv[0];
	sys.exit(1);

def obfuscate(mapper, fname, overwrite, _):
	with open(fname, 'rU') as fp:
		tree = Obfuscator(mapper).obfuscate(fp);
	p = io.BytesIO();
	unparse.Unparser(tree, p);
	if not overwrite:
		base, ext = os.path.splitext(fname);
		shutil.copyfile(fname, base + '.backup' + ext);
	with open(fname, 'w') as fp:
		fp.write(p.getvalue());

def obfuscateAll(mapper, root, overwrite, ignore):
	for name in os.listdir(root):
		path = os.path.join(root, name);
		if path not in ignore:
			if os.path.isfile(path) and name.endswith('.py'):
				obfuscate(mapper, path, overwrite, None);
			elif os.path.isdir(path):
				obfuscateAll(mapper, path, overwrite, ignore);

try:
	opts, args = getopt.getopt(sys.argv[1:], 'horx:', ['help', 'overwrite', 'recursive', 'exclude=']);
except getopt.GetoptError:
	usage();

if len(args) == 0:
	usage();

ignore = [];
mapper = {};
overwrite = False;
processor = obfuscate;

for opt, arg in opts:
	if opt in ('-h', '--help'):
		usage();
	if opt in ('-x', '--exclude'):
		ignore.append(arg);
	elif opt in ('-o', '--overwrite'):
		overwrite = True;
	elif opt in ('-r', '--recursive'):
		processor = obfuscateAll;

for arg in args:
	processor(mapper, arg, overwrite, ignore);
