/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0

#include <libsolidity/analysis/ControlFlowRevertPruner.h>

#include <libsolutil/Algorithms.h>

#include <range/v3/algorithm/remove.hpp>


namespace solidity::frontend
{

namespace
{

/// Find the right scope for the called function: When calling a base function,
/// we keep the most derived, but we use the called contract in case it is a
/// library function or nullptr for a free function.
ContractDefinition const* findScopeContract(CallableDeclaration const& _callable, ContractDefinition const* _callingContract)
{
	if (auto const* functionContract = _callable.annotation().contract)
	{
		if (_callingContract && _callingContract->derivesFrom(*functionContract))
			return _callingContract;
		else
			return functionContract;
	}

	return nullptr;
}
}

void ControlFlowRevertPruner::run()
{
	for (auto& [pair, flow]: m_cfg.allFunctionFlows())
		m_callables[pair] = RevertState::Unknown;

	findRevertStates();
	modifyFunctionFlows();
}

ModifierDefinition const* resolveModifierInvocation(ModifierInvocation const& _invocation, ContractDefinition const& _contract);
ModifierDefinition const* resolveModifierInvocation(ModifierInvocation const& _invocation, ContractDefinition const& _contract)
{
	if (auto const* modifier = dynamic_cast<ModifierDefinition const*>(_invocation.name().annotation().referencedDeclaration))
	{
		VirtualLookup const& requiredLookup = *_invocation.name().annotation().requiredLookup;

		if (requiredLookup == VirtualLookup::Virtual)
			return &modifier->resolveVirtual(_contract);
		else
		{
			solAssert(requiredLookup == VirtualLookup::Static, "");
			return modifier;
		}
	}

	return nullptr;
}

void ControlFlowRevertPruner::findRevertStates()
{
	std::set<CFG::ContractCallableTuple> pendingFunctions = keys(m_callables);
	// We interrupt the search whenever we encounter a call to a function with (yet) unknown
	// revert behaviour. The ``wakeUp`` data structure contains information about which
	// searches to restart once we know about the behaviour.
	std::map<CFG::ContractCallableTuple, std::set<CFG::ContractCallableTuple>> wakeUp;

	while (!pendingFunctions.empty())
	{
		CFG::ContractCallableTuple item = *pendingFunctions.begin();
		pendingFunctions.erase(pendingFunctions.begin());

		if (m_callables[item] != RevertState::Unknown)
			continue;

		bool foundExit = false;
		bool foundUnknown = false;
		bool foundPlaceholder = false;

		FunctionFlow const& functionFlow = m_cfg.functionFlow(*item.callable, item.contract);

		solidity::util::BreadthFirstSearch<CFGNode*>{{functionFlow.entry}}.run(
			[&](CFGNode* _node, auto&& _addChild) {
				if (_node == functionFlow.exit)
					foundExit = true;
				if (_node->placeholderStatement)
				{
					foundPlaceholder = true;
					solAssert(_node != functionFlow.exit, "Placeholder cannot be an exit node!");
				}

				ModifierDefinition const* modifier = nullptr;
				FunctionDefinition const* function = nullptr;
				CallableDeclaration const* callable = nullptr;

				if (_node->modifierInvocation)
					callable = modifier = resolveModifierInvocation(*_node->modifierInvocation, *item.contract);
				if (_node->functionCall)
					callable = function = ASTNode::resolveFunctionCall(*_node->functionCall, item.contract);

				solAssert(!modifier || !function, "Node can only have modifier or function.");

				if (
					(modifier && modifier->isImplemented()) ||
					(function && function->isImplemented())
				)
				{
					CFG::ContractCallableTuple calledCallableTuple{
						findScopeContract(*callable, item.contract),
						callable
					};
					switch (m_callables.at(calledCallableTuple))
					{
						case RevertState::Unknown:
							wakeUp[calledCallableTuple].insert(item);
							foundUnknown = true;
							return;
						case RevertState::AllPathsRevert:
							return;
						case RevertState::HasNonRevertingPath:
							break;
						case RevertState::ModifierRevertPassthrough:
							solAssert(
								dynamic_cast<ModifierDefinition const*>(callable),
								"Invalid state for function flow."
							);
							break;
					}
				}

				for (CFGNode* exit: _node->exits)
					_addChild(exit);
			}
		);

		auto& revertState = m_callables[item];

		if (foundExit)
		{
			if (foundPlaceholder)
				revertState = RevertState::ModifierRevertPassthrough;
			else
				revertState = RevertState::HasNonRevertingPath;
		}
		else if (!foundUnknown)
			revertState = RevertState::AllPathsRevert;

		if (revertState != RevertState::Unknown && wakeUp.count(item))
		{
			// Restart all searches blocked by this function.
			for (CFG::ContractCallableTuple const& nextItem: wakeUp[item])
				if (m_callables.at(nextItem) == RevertState::Unknown)
					pendingFunctions.insert(nextItem);
			wakeUp.erase(item);
		}
	}
}

void ControlFlowRevertPruner::modifyFunctionFlows()
{
	for (auto& item: m_callables)
	{
		FunctionFlow const& functionFlow = m_cfg.functionFlow(*item.first.callable, item.first.contract);
		solidity::util::BreadthFirstSearch<CFGNode*>{{functionFlow.entry}}.run(
			[&](CFGNode* _node, auto&& _addChild) {
				if (auto const* functionCall =  _node->functionCall)
				{
					auto const* resolvedFunction = ASTNode::resolveFunctionCall(*functionCall, item.first.contract);

					if (resolvedFunction && resolvedFunction->isImplemented())
						switch (m_callables.at({findScopeContract(*resolvedFunction, item.first.contract), resolvedFunction}))
						{
							case RevertState::Unknown:
								[[fallthrough]];
							case RevertState::AllPathsRevert:
								// If the revert states of the functions do not
								// change anymore, we treat all "unknown" states as
								// "reverting", since they can only be caused by
								// recursion.
								for (CFGNode * node: _node->exits)
									ranges::remove(node->entries, _node);

								_node->exits = {functionFlow.revert};
								functionFlow.revert->entries.push_back(_node);
								return;
							default:
								break;
						}
				}

				for (CFGNode* exit: _node->exits)
					_addChild(exit);
		});
	}
}

}
